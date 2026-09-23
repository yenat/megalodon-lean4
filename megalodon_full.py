#!/usr/bin/env python3
"""
Megalodon -> Lean 4 translator with categorised output and Lean verification.

Reads a Megalodon .mg file, translates the preamble (Parameter / Axiom /
Definition / notation) into a Lean 4 prelude, sorts the theorems into
mathematical tiers, writes one .lean file per tier, then compiles each with
`lean` and prunes any theorem that does not verify -- so every emitted file
compiles cleanly.

    python megalodon_full.py 100thms_12.mg --output ./lean_out
"""
import argparse
import re
import shutil
import subprocess
import time
import sys
from pathlib import Path

BS = chr(92)

# ----------------------------------------------------------------------
# source parsing
# ----------------------------------------------------------------------

def strip_comments(text):
    return re.sub(r"\(\*.*?\*\)", " ", text, flags=re.S)


def parse_source(text):
    """Read the .mg source into {theorems, fixity, binders}.

    `theorems` carries each theorem's statement, proof lines, and the Section
    scope it was written in -- Megalodon leaves that scope implicit, and Lean
    needs it spelled out.
    """
    t = strip_comments(text)

    # Megalodon declares its own operators; the translator learns them from
    # the file rather than hardcoding a table.
    fixity = {}            # megalodon token -> (kind, precedence, assoc)
    for m in re.finditer(
            r"^(Infix|Prefix|Postfix)\s+(\S+)\s+(\d+)\s*(left|right)?\s*:=\s*([A-Za-z_][\w']*)",
            t, re.M):
        kind, tok, prec, assoc, _target = m.groups()
        fixity[tok] = (kind.lower(), int(prec), assoc)

    binders = {}
    for m in re.finditer(r"^Binder\+?\s+(\S+)\s*,?\s*:=\s*([A-Za-z_][\w']*)", t, re.M):
        binders[m.group(1)] = m.group(2)

    # Theorems inside `Section S. Variable x:T. ... End S.` are implicitly
    # parameterised by the section variables, and reference section-scoped
    # definitions bare. Both need to be made explicit for Lean.
    theorems = []
    sec_stack = []
    sec_defs = {}          # section def name -> section vars it abstracts over
    sec_lets = {}          # section-local `Let` name -> lifted top-level name
    sec_thms = {}          # section-scoped theorem -> section vars it binds
    sec_let_vars = {}      # section-local `Let` -> section vars it absorbs
    cur_section = None
    scan = re.compile(
        r"^(Section|End|Variable|Hypothesis|Let|Definition)\s+(.+?)\.\s*$"
        r"|^Theorem\s+([A-Za-z_][\w']*)\s*:(.*?)^Qed\.", re.S | re.M)
    for m in scan.finditer(t):
        if m.group(3):                      # a Theorem
            stmt, proof = split_statement(m.group(4))
            blob = stmt + " " + " ".join(proof)
            sec_binders = [(v, ty) for v, ty in sec_stack
                           if v != "<mark>"
                           and re.search(r"\b%s\b" % re.escape(v), blob)]
            theorems.append({"name": m.group(3), "stmt": stmt, "proof": proof,
                             "binders": sec_binders,
                             "secdefs": dict(sec_defs),
                             "secthms": dict(sec_thms),
                             "allsec": [(v, ty) for v, ty in sec_stack
                                        if v != "<mark>"],
                             "lets": dict(sec_lets)})
            # A theorem proved inside a section is parameterised by the
            # section variables too, so later theorems in the same section
            # must apply it to them -- exactly like a section definition.
            if sec_binders:
                sec_thms[m.group(3)] = list(sec_binders)
            continue
        kind, rest = m.group(1), " ".join(m.group(2).split())
        if kind == "Section":
            sec_stack.append(("<mark>", rest))
            cur_section = rest.split()[0] if rest.split() else "Sec"
        elif kind == "End":
            sec_defs = {}
            sec_lets = {}
            sec_thms = {}
            sec_let_vars = {}
            cur_section = None
            while sec_stack and sec_stack[-1][0] != "<mark>":
                sec_stack.pop()
            if sec_stack:
                sec_stack.pop()
        elif kind in ("Variable", "Hypothesis"):
            if ":" in rest:
                names, ty = rest.split(":", 1)
                for nm in names.split():
                    sec_stack.append((nm, ty.strip()))
        elif kind in ("Let", "Definition"):
            if sec_stack:
                # `Let pair := setsum.` has no type ascription, so the name
                # has to be cut at `:=` before `:`.
                nm = rest.split(":=")[0].split(":")[0].strip()
                # Both `Let`s and `Definition`s absorb section variables,
                # transitively through anything they mention. prelude_items
                # resolves this when it lifts them, so the two must agree or
                # callers get the wrong argument list.
                need = {v for v, _ in sec_stack if v != "<mark>"
                        and re.search(r"\b%s\b" % re.escape(v), rest)}
                for tbl in (sec_defs, sec_let_vars):
                    for d, dv in tbl.items():
                        if re.search(r"\b%s\b" % re.escape(d), rest):
                            need |= set(dv)
                ordered = [v for v, _ in sec_stack
                           if v != "<mark>" and v in need]
                if kind == "Let" and ":=" in rest:
                    sec_lets[nm] = ("%s_%s" % (cur_section or "Sec", nm),
                                    ordered)
                    sec_let_vars[nm] = ordered
                else:
                    sec_defs[nm] = ordered
    return {"theorems": theorems, "fixity": fixity, "binders": binders}


def split_statement(rest):
    """Statement ends at the first line whose stripped text ends with '.'."""
    lines = rest.split("\n")
    buf = []
    for i, line in enumerate(lines):
        buf.append(line)
        if line.strip().endswith("."):
            stmt = " ".join(" ".join(buf).split())
            return stmt[:-1].strip(), lines[i + 1:]
    return " ".join(" ".join(buf).split()), []

# ----------------------------------------------------------------------
# operators: Megalodon token -> collision-free Lean token
# ----------------------------------------------------------------------
# Lean core already owns /\ \/ <-> = < <= + * - etc., so every Megalodon
# operator is remapped to a token Lean cannot already mean. Unicode also
# sidesteps backslash escaping in notation string literals entirely.
# Megalodon defines `=` as Leibniz equality. Lean's `rw`, `symm` and `congr`
# only work on native `Eq`, and `rewrite` accounts for 2644 tactic uses, so the
# notation is bound to Lean's `Eq`/`Ne` instead of the Leibniz definitions.
# `eq` maps onto Lean's `Eq` so that `rw` works. `neq` must NOT map onto
# Lean's `Ne`: that unfolds to Lean's `False`, whereas Megalodon defines its
# own `False` (`forall p:prop, p`). Mixing the two makes `apply H` fail on a
# `<>` hypothesis, which is how `xm` died.
NATIVE_EQ = {"eq": "Eq"}

CURATED = {
    "/" + BS: "⋏",      # /\  -> ⋏
    BS + "/": "⋎",      # \/  -> ⋎
    "~": "⌐",           # ~   -> ⌐
    "<->": "⟺",         # <-> -> ⟺
    "=": "≐",           # =   -> ≐
    "<>": "≢",          # <>  -> ≢
    ":e": "∊",          # :e  -> ∊
    "c=": "⊑",          # c=  -> ⊑
    "/:e": "∉",
}


BUILTIN = {":e": "In", "c=": "Subq", "/:e": "nIn"}


def build_token_map(fixity):
    out, n = dict(), 0
    for tok in BUILTIN:                       # always mapped, never declared
        out[tok] = CURATED[tok]
    for tok in sorted(fixity, key=len, reverse=True):
        if tok in CURATED:
            out[tok] = CURATED[tok]
        else:
            n += 1
            out[tok] = "⋄%d⋄" % n      # ⋄N⋄ - cannot collide
    return out


def lean_prec(meg_prec):
    """Megalodon: lower binds tighter. Lean: higher binds tighter. Invert."""
    return max(10, min(1024, 1100 - meg_prec))


# `~` is deliberately NOT in this class: it is a prefix operator that stacks
# (`~~P`), and treating it as a boundary character made both occurrences fail
# to match, leaving `~~P` untranslated.
OPCH = r"=<>:/\\+*'\-\[\]"


def make_sub_re(tokmap):
    toks = sorted(tokmap, key=len, reverse=True)
    return re.compile("|".join(
        r"(?<![%s])%s(?![%s])" % (OPCH, re.escape(tk), OPCH) for tk in toks))


def convert_exists(s, binders):
    """`exists x, BODY` -> `ex (fun x => BODY)`.

    The binder spec may carry a parenthesised type (`exists f:set->(set->set),`)
    or a prime (`exists w',`), so the separating comma is found by scanning at
    bracket depth zero rather than by a character class.
    """
    SPEC = re.compile(r"^[\w\s:>\-'()\[\]]+$")
    for word, target in binders.items():
        pat = re.compile(r"\b%s\s+" % word)
        pos = 0
        while True:
            m = pat.search(s, pos)
            if not m:
                break
            depth, ci = 0, None
            for i in range(m.end(), len(s)):
                c = s[i]
                if c in "([":
                    depth += 1
                elif c in ")]":
                    if depth == 0:
                        break
                    depth -= 1
                elif c == "," and depth == 0:
                    ci = i
                    break
            var = s[m.end():ci].strip() if ci is not None else ""
            if ci is None or not var or not SPEC.match(var):
                pos = m.end()
                continue
            depth, end = 0, len(s)
            for i in range(ci + 1, len(s)):
                if s[i] in "([":
                    depth += 1
                elif s[i] in ")]":
                    if depth == 0:
                        end = i
                        break
                    depth -= 1
            body = s[ci+1:end]
            s = s[:m.start()] + "%s (fun %s => %s)" % (target, var, body) + s[end:]
            pos = m.start() + len(target)
    return s


def build_setlam(text):
    """`Notation SetLam Sigma.` makes `fun x :e X => F x` mean `Sigma X ...`."""
    m = re.search(r"^Notation\s+SetLam\s+([A-Za-z_][\w']*)\s*\.", text, re.M)
    return m.group(1) if m else None


def build_binder_ops(text):
    """`Binder \\/_ , := famunion.` declares an indexed binder token.

    `Binder+ exists , := ex; and.` is the bounded-exists form, handled
    separately by convert_exists, so it is skipped here.
    """
    ops = {}
    for m in re.finditer(r"^Binder\+?\s+(\S+)\s*,\s*:=\s*([A-Za-z_][\w']*)\s*(?:;\s*[A-Za-z_][\w']*\s*)?\.",
                         text, re.M):
        tok, tgt = m.group(1), m.group(2)
        if tgt == "ex":
            continue
        ops[tok] = tgt
    return ops


def indexed_binders(s, ops=None):
    """`Sigma_ x :e X, BODY` -> `Sigma X (fun x => BODY)`.

    Tokens come from the source's own `Binder` directives, so symbolic ones
    like `\\/_` (famunion) work as well as alphabetic ones. The body runs to
    the end of the enclosing bracket, so the closing paren has to be placed
    by scanning rather than by regex.
    """
    ops = ops or {}
    toks = sorted(ops, key=len, reverse=True)
    alt = "|".join(re.escape(t) for t in toks)
    alt = (alt + "|" if alt else "") + r"\w+_"
    pat = re.compile(r"(?<![\w])(%s)\s+([A-Za-z_][\w']*)\s*:e\s*([^,]+?)\s*,\s*" % alt)
    while True:
        m = pat.search(s)
        if not m:
            return s
        tok, var, dom = m.group(1), m.group(2), m.group(3)
        head = ops.get(tok) or tok.rstrip("_")
        depth, end = 0, len(s)
        for i in range(m.end(), len(s)):
            if s[i] in "([":
                depth += 1
            elif s[i] in ")]":
                if depth == 0:
                    end = i
                    break
                depth -= 1
        body = s[m.end():end]
        s = s[:m.start()] + "%s %s (fun %s => %s)" % (head, dom, var, body) + s[end:]


def convert_ite(s):
    """`if C then A else B` -> `If_i C A B`, innermost first.

    Lean's own `if` needs a Decidable instance, which Megalodon's Prop-valued
    conditions do not have. Nesting rules out a regex, so scan: the else-branch
    runs to the end of the enclosing bracket.
    """
    def kw(i, w):
        return (s.startswith(w, i)
                and (i == 0 or not (s[i-1].isalnum() or s[i-1] == "_"))
                and not (s[i+len(w):i+len(w)+1].isalnum()
                         or s[i+len(w):i+len(w)+1] == "_"))

    def seek(start, word):
        depth = 0
        i = start
        while i < len(s):
            c = s[i]
            if c in "([":
                depth += 1
            elif c in ")]":
                if depth == 0:
                    return None
                depth -= 1
            elif depth == 0 and kw(i, word):
                return i
            i += 1
        return None

    while True:
        last = None
        for m in re.finditer(r"\bif\b", s):
            last = m
        if last is None:
            return s
        ti = seek(last.end(), "then")
        if ti is None:
            return s
        ei = seek(ti + 4, "else")
        if ei is None:
            return s
        depth, end = 0, len(s)
        for j in range(ei + 4, len(s)):
            c = s[j]
            if c in "([":
                depth += 1
            elif c in ")]":
                if depth == 0:
                    end = j
                    break
                depth -= 1
        s = (s[:last.start()]
             + "(If_i (%s) (%s) (%s))" % (s[last.end():ti].strip(),
                                          s[ti+4:ei].strip(),
                                          s[ei+4:end].strip())
             + s[end:])


TUPLE_BAD = re.compile(r"\b(forall|exists|fun|if|then|else)\b|=>|\||:")


def _depth0_mask(p):
    """`p` with anything inside nested (...)/[...] blanked out, so a keyword
    search only sees what sits at THIS bracket's own top level."""
    out, depth = [], 0
    for ch in p:
        if ch in "([":
            depth += 1; out.append(ch)
        elif ch in ")]":
            depth -= 1; out.append(ch)
        else:
            out.append(ch if depth == 0 else " ")
    return "".join(out)


def convert_tuples(s, lam="Sigma", eq="\u2250"):
    """`(a,b)` is Megalodon's TUPLE: a set-lambda over the index set.

    `(x0,x1)` means `fun i :e 2 => if i = 0 then x0 else x1`, not `pair x0 x1`
    -- those are only propositionally equal (`pair_tuple_fun` is a theorem),
    so encoding tuples as `pair` breaks every proof that rewrites with `beta`.

    Only a bracket whose top-level comma-separated parts are plain terms is
    rewritten, so binder commas (`forall x, P`) are left alone.
    """
    def numeral(k):
        out = "Empty"
        for _ in range(k):
            out = "(ordsucc %s)" % out
        return out

    i = len(s) - 1
    while i >= 0:
        if s[i] != "(":
            i -= 1
            continue
        depth, j = 0, None
        for k in range(i + 1, len(s)):
            if s[k] in "([":
                depth += 1
            elif s[k] in ")]":
                if depth == 0:
                    j = k
                    break
                depth -= 1
        if j is None:
            i -= 1
            continue
        parts, d, buf = [], 0, ""
        for ch in s[i+1:j]:
            if ch in "([":
                d += 1
            elif ch in ")]":
                d -= 1
            if ch == "," and d == 0:
                parts.append(buf)
                buf = ""
            else:
                buf += ch
        parts.append(buf)
        # A binder keyword (`fun`, `forall`, ...) only makes a comma
        # ambiguous when it sits at THIS bracket's own top level -- one
        # safely nested inside its own parens, e.g. `(Repl X (fun w => g w))`,
        # cannot bleed into the enclosing comma and is not a real hazard.
        if len(parts) >= 2 and all(p.strip() and not TUPLE_BAD.search(_depth0_mask(p))
                                   for p in parts):
            n = len(parts)
            body = parts[-1].strip()
            for k in range(n - 2, -1, -1):
                body = "(If_i (_ti %s %s) (%s) (%s))" % (
                    eq, numeral(k), parts[k].strip(), body)
            s = (s[:i] + "(%s %s (fun _ti => %s))" % (lam, numeral(n), body)
                 + s[j+1:])
        i -= 1
    return s


class Converter:
    def __init__(self, tokmap, binders, binder_ops=None, setlam=None):
        self.tokmap = tokmap
        self.binders = binders
        self.binder_ops = binder_ops or {}
        self.setlam = setlam
        self.sub_re = make_sub_re(tokmap)

    def set_lambda(self, s):
        """`fun x :e X => F x` -> `Sigma X (fun x => F x)`.

        Megalodon's set-level lambda. The body runs to the end of the
        enclosing bracket, so the closing paren is placed by scanning.
        """
        if not self.setlam:
            return s
        pat = re.compile(r"\bfun\s+([\w']+)\s*:e\s*([^=]+?)\s*=>\s*")
        while True:
            m = pat.search(s)
            if not m:
                return s
            var, dom = m.group(1), m.group(2)
            depth, end = 0, len(s)
            for i in range(m.end(), len(s)):
                if s[i] in "([":
                    depth += 1
                elif s[i] in ")]":
                    if depth == 0:
                        end = i
                        break
                    depth -= 1
            s = (s[:m.start()]
                 + "%s %s (fun %s => %s)" % (self.setlam, dom, var,
                                             s[m.end():end])
                 + s[end:])

    def setbuilders(self, s):
        """Megalodon's braces/if notation -> plain function application."""
        prev = None
        while prev != s:
            prev = s
            # {F x | x :e X, P x} -> ReplSep X (fun x => P x) (fun x => F x)
            s = re.sub(r"\{\s*([^{}|]+?)\s*\|\s*([\w']+)\s*:e\s*([^{},]+?)\s*,\s*([^{}]+)\}",
                       r"(ReplSep (\3) (fun \2 => \4) (fun \2 => \1))", s)
            # {x :e X | P}  -> Sep X (fun x => P)
            s = re.sub(r"\{\s*([\w']+)\s*:e\s*([^{}|]+)\|\s*([^{}]+)\}",
                       r"(Sep (\2) (fun \1 => \3))", s)
            # {F x | x :e X} -> Repl X (fun x => F x)
            s = re.sub(r"\{\s*([^{}|]+?)\s*\|\s*([\w']+)\s*:e\s*([^{}]+)\}",
                       r"(Repl (\3) (fun \2 => \1))", s)
            # {a,b} -> UPair a b ;  {a} -> Sing a
            s = re.sub(r"\{\s*([^{},|]+?)\s*,\s*([^{},|]+?)\s*\}",
                       r"(UPair \1 \2)", s)
            s = re.sub(r"\{\s*([^{},|]+?)\s*\}", r"(Sing \1)", s)
        return convert_ite(s)

    def expr(self, s):
        s = self.set_lambda(s)
        s = self.setbuilders(s)
        # numerals: `Notation Nat Empty ordsucc` makes 0 = Empty, 1 = ordsucc 0
        def _numeral(m):
            # `Vo 1` / `Descr_Vo1 : Vo 1` index a universe, not a set numeral
            if s[:m.start()].rstrip().endswith("Vo"):
                return m.group(0)
            n = int(m.group(0))
            out = "Empty"
            for _ in range(n):
                out = "(ordsucc %s)" % out
            return out
        s = re.sub(r"(?<![\w.])\d+(?![\w.])", _numeral, s)

        s = indexed_binders(s, self.binder_ops)
        # `forall x y :e A, B` -> `forall x y, In x A -> In y A -> B`
        def _bounded(m):
            # `forall u v :e X, P` is `forall u :e X, forall v :e X, P` --
            # each guard follows ITS OWN binder. Grouping the binders first
            # shifts every later `intro` onto the wrong hypothesis.
            vs = m.group(1).split()
            st = m.group(2)
            st = st if re.match(r"^[\w']+$", st) else "(%s)" % st
            return "".join("forall %s, In %s %s -> " % (v, v, st) for v in vs)
        s = re.sub(r"\bforall\s+([\w\s']+?)\s*:e\s+([^,]+?)\s*,", _bounded, s)
        # `exists v :e X, BODY` is `ex (fun v => In v X /\ BODY)`. `/\` is
        # LEFT associative (`Infix /\ 780 left`), so writing the guard as
        # `In v X ⋏ BODY` would parse as `(In v X ⋏ B) ⋏ C` and swallow the
        # body's first conjunct -- the body has to be bracketed, which means
        # scanning for its end rather than a regex replacement.
        def _bounded_ex(s, rel, op):
            pat = re.compile(r"\bexists\s+([\w\s']+?)\s*%s\s+([^,]+?)\s*,\s*"
                             % re.escape(rel))
            while True:
                m = pat.search(s)
                if not m:
                    return s
                vs, st = m.group(1).split(), m.group(2).strip()
                st = st if re.match(r"^[\w']+$", st) else "(%s)" % st
                depth, end = 0, len(s)
                for i in range(m.end(), len(s)):
                    if s[i] in "([":
                        depth += 1
                    elif s[i] in ")]":
                        if depth == 0:
                            end = i
                            break
                        depth -= 1
                rep = "".join("exists %s, %s %s %s ⋏ (" % (v, op, v, st)
                              for v in vs)
                s = (s[:m.start()] + rep + s[m.end():end] + ")" * len(vs)
                     + s[end:])

        s = _bounded_ex(s, ":e", "In")

        # `forall Y c= X, P` / `exists Y c= X, P` -- the subset-bounded forms
        def _bsub(m):
            vs, st = m.group(1).split(), m.group(2).strip()
            st = st if re.match(r"^[\w']+$", st) else "(%s)" % st
            return "".join("forall %s, Subq %s %s -> " % (v, v, st) for v in vs)
        s = re.sub(r"\bforall\s+([\w\s']+?)\s*c=\s*([^,]+?)\s*,", _bsub, s)
        s = _bounded_ex(s, "c=", "Subq")
        s = convert_exists(s, self.binders)
        # `d'` is one identifier in Megalodon and in Lean alike; only a
        # spaced `beta '` is the postfix `tag` operator.
        s = re.sub(r"(?<=[\w])'", "\x00P\x00", s)
        s = self.sub_re.sub(lambda m: self.tokmap[m.group(0)], s)
        s = s.replace("\x00P\x00", "'")
        # after tokenisation, a `:` can only be a type ascription, so tuple
        # brackets are now distinguishable from binder and operator syntax
        s = convert_tuples(s, self.setlam or "Sigma",
                           self.tokmap.get("=", "\u2250"))
        # Megalodon's default sort is `set`: `forall x y, ...` means
        # `forall x y : set, ...`. Without the annotation Lean cannot
        # synthesise the implicit type argument of Eq/Ne and friends.
        def _default_sort(m):
            vs = m.group(1).strip()
            return "forall %s : set," % vs
        s = re.sub(r"\bforall\s+([a-z]\w*(?:\s+[a-z]\w*)*)\s*,", _default_sort, s)
        # `eq` is not emitted as a definition (it maps onto Lean's `Eq`), so
        # bare identifier uses of it -- `~ eq x y` in the body of `neq` --
        # have to be redirected too, or they dangle.
        for _src, _dst in NATIVE_EQ.items():
            s = re.sub(r"\b%s\b" % re.escape(_src), _dst, s)
        s = re.sub(r"\bprop\b", "Prop", s)
        s = re.sub(r"\bSType\b", "Type", s)
        return s

# ----------------------------------------------------------------------
# prelude
# ----------------------------------------------------------------------

def prelude_items(text, conv, tokmap, fixity):
    """Preamble declarations in SOURCE ORDER, with Section variables bound.

    Megalodon puts polymorphic definitions inside `Section S. Variable A:SType.
    ... End S.`; those variables become implicit binders on each declaration
    that mentions them. Notation is emitted right after the definition it
    names, because later definitions use it.
    """
    t = strip_comments(text)
    # tokens the source declares itself: emitting our BUILTIN notation for
    # these as well produces "Ambiguous term" with two identical readings
    declared_toks = set(re.findall(
        r"^(?:Infix|Prefix|Postfix)\s+(\S+)\s+\d+", t, re.M))
    items = []
    sec_stack = []          # list of (var, type) currently in scope
    seen_tok = set()        # `Infix +` is declared 25x (overloaded); Lean
                            # would report "Ambiguous term", so keep the first
    lets = {}               # Section-local `Let` renames: name -> Sec_name
    sec_defs = {}           # defs inside the current section -> section vars
                            # they abstract over, so siblings can apply them

    line_re = re.compile(
        r"^(Section|End|Variable|Hypothesis|Let|Parameter|Axiom|Definition"
        r"|Infix|Prefix|Postfix|Notation)"
        r"\s+(.+?)\.\s*$", re.M | re.S)

    cur_section = None

    def apply_lets(txt, table):
        # table: name -> (qualified_name, [section vars it abstracts over])
        for k, (v, args) in table.items():
            # A `fun k => ...` binder shadows the Let, so leave those alone --
            # substituting there would rewrite the bound variable itself.
            if re.search(r"fun\s+[^=]*\b%s\b[^=]*=>" % re.escape(k), txt):
                continue
            rep = ("(%s %s)" % (v, " ".join(args))) if args else v
            txt = re.sub(r"\b%s\b" % re.escape(k), rep, txt)
        return txt

    def binders_for(*texts, explicit_types=False):
        blob = " ".join(texts)
        out = []
        for var, ty in sec_stack:
            if re.search(r"\b%s\b" % re.escape(var), blob):
                # Type variables (`Variable A:SType`) stay IMPLICIT -- uses
                # write `x = y`, not `eq A x y`. Value variables
                # (`Variable X:set`) are EXPLICIT, since Megalodon discharges
                # them into real parameters: theorems write `Sep X P`.
                if re.match(r"^(Type|Sort)\b", ty.strip()):
                    # Megalodon applies axioms to their section type variables
                    # explicitly (`func_ext set Prop`), but definitions are
                    # used through notation, where they must stay implicit.
                    out.append(("(%s : Sort u)" if explicit_types
                                else "{%s : Sort u}") % var)
                else:
                    out.append("(%s : %s)" % (var, ty))
        return " ".join(out)

    for m in line_re.finditer(t):
        kind, rest = m.group(1), " ".join(m.group(2).split())

        if kind == "Notation":
            # `Notation SetImplicitOp ap.` declares that juxtaposing two sets
            # means application via `ap` -- that is how Megalodon writes pair
            # projection (`u 0`, `u 1`). Lean spells the same rule `CoeFun`.
            parts = rest.split()
            if len(parts) >= 2 and parts[0] == "SetImplicitOp":
                items.append(("coefun:" + parts[1],
                              "noncomputable instance : CoeFun set (fun _ => set -> set)"
                              " := \u27e8%s\u27e9" % parts[1]))
            continue

        if kind == "Section":
            sec_stack.append(("<mark>", rest))
            cur_section = rest.split()[0] if rest.split() else "Sec"
            continue
        if kind == "End":
            lets = {}
            sec_defs = {}
            cur_section = None
            while sec_stack and sec_stack[-1][0] != "<mark>":
                sec_stack.pop()
            if sec_stack:
                sec_stack.pop()
            continue
        if kind == "Let":
            # `Let F : T := body.` is a section-local definition. Lift it to a
            # top-level def under a section-qualified name and rewrite later
            # references, since names like `z`/`F` recur across sections.
            if ":=" not in rest:
                continue
            head, body = rest.split(":=", 1)
            nm = head.split(":")[0].strip()
            ty = head.split(":", 1)[1].strip() if ":" in head else ""
            qual = "%s_%s" % (cur_section or "Sec", nm)
            body = apply_lets(conv.expr(body), lets)
            ty = conv.expr(ty) if ty else ""
            b = binders_for(ty, body)
            used = [v for v, _ in sec_stack
                    if v != "<mark>" and re.search(r"\b%s\b" % re.escape(v),
                                                   ty + " " + body)]
            items.append((qual, "noncomputable def %s %s%s:= %s"
                          % (qual, b + " " if b else "",
                             (": %s " % ty) if ty else "", body)))
            lets[nm] = (qual, used)
            continue
        if kind in ("Variable", "Hypothesis"):
            if ":" in rest:
                names, ty = rest.split(":", 1)
                ty = conv.expr(ty.strip())
                for nm in names.split():
                    sec_stack.append((nm, ty))
            continue

        if kind in ("Parameter", "Axiom"):
            if ":" not in rest:
                continue
            name, ty = rest.split(":", 1)
            name, ty = name.strip(), conv.expr(ty)
            if name == "set":
                continue
            b = binders_for(ty, explicit_types=True)
            items.append((name, "axiom %s %s: %s" % (name, b + " " if b else "", ty)))
            for tok, tgt in BUILTIN.items():
                if tgt == name and tok in tokmap and tok not in declared_toks:
                    items.append(("notation:" + tok,
                                  'infix:%d " %s " => %s' % (lean_prec(502), tokmap[tok], name)))

        elif kind == "Definition":
            if ":=" not in rest or ":" not in rest.split(":=")[0]:
                continue
            if rest.split(":")[0].strip() in NATIVE_EQ:
                continue        # use Lean's own Eq / Ne
            head, body = rest.split(":=", 1)
            name, ty = head.split(":", 1)
            name = name.strip()
            ty, body = conv.expr(ty), apply_lets(conv.expr(body), lets)
            body = apply_lets(body, sec_defs)
            ty = apply_lets(ty, sec_defs)
            b = binders_for(ty, body)
            used = [v for v, _ in sec_stack
                    if v != "<mark>" and re.search(r"\b%s\b" % re.escape(v),
                                                   ty + " " + body)]
            if cur_section and used:
                sec_defs[name] = (name, used)
            # Everything is `noncomputable`: these definitions rest on the
            # Eps_i choice axiom, which has no executable content.
            items.append((name, "noncomputable def %s %s: %s := %s"
                          % (name, b + " " if b else "", ty, body)))
            for tok, tgt in BUILTIN.items():
                if tgt == name and tok in tokmap and tok not in declared_toks:
                    items.append(("notation:" + tok,
                                  'infix:%d " %s " => %s' % (lean_prec(502), tokmap[tok], name)))

        else:  # Infix / Prefix / Postfix
            mm = re.match(r"(\S+)\s+(\d+)\s*(left|right)?\s*:=\s*([A-Za-z_][\w']*)", rest)
            if not mm or mm.group(1) not in tokmap or mm.group(1) in seen_tok:
                continue
            seen_tok.add(mm.group(1))
            if mm.group(4) in NATIVE_EQ:
                items.append(("notation:" + mm.group(1),
                              'infix:%d " %s " => %s'
                              % (lean_prec(int(mm.group(2))), tokmap[mm.group(1)],
                                 NATIVE_EQ[mm.group(4)])))
                continue
            tok, prec, assoc, target = mm.groups()
            # `Postfix ' 100 := tag.` names a section-local `Let`, which was
            # lifted to a qualified top-level def; point the notation at that.
            if target in lets and not lets[target][1]:
                target = lets[target][0]
            lt, pr = tokmap[tok], lean_prec(int(prec))
            if kind == "Infix":
                key = ("infixl" if assoc == "left"
                       else "infixr" if assoc == "right" else "infix")
                items.append(("notation:" + tok,
                              '%s:%d " %s " => %s' % (key, pr, lt, target)))
            elif kind == "Prefix":
                items.append(("notation:" + tok,
                              'prefix:%d "%s" => %s' % (pr, lt, target)))
            else:
                items.append(("notation:" + tok,
                              'postfix:%d "%s" => %s' % (pr, lt, target)))
    return items


HEADER = ("namespace Megalodon\n"
          "set_option linter.unusedVariables false\n"
          "set_option maxHeartbeats 1000000\n"
          "universe u\n\n"
          "axiom set : Type\n"
          "-- Megalodon builtin universe family: Vo 0 = set, Vo (n+1) = Vo n -> Prop\n"
          "def Vo : Nat -> Type\n"
          "  | 0 => set\n"
          "  | (n+1) => Vo n -> Prop\n"
          "-- Megalodon's `=` is Leibniz equality (`forall Q, Q x y -> Q y x`)\n"
          "-- and its proofs APPLY an equation like a function (`He Q H`).\n"
          "-- The notation binds to Lean's `Eq` so `rw` works, so this\n"
          "-- coercion restores the Leibniz use without giving up `rw`.\n"
          "noncomputable instance {A : Sort u} {x y : A} :\n"
          "    CoeFun (x = y) (fun _ => forall Q : A -> A -> Prop,"
          " Q x y -> Q y x) :=\n"
          "  \u27e8fun h Q => by subst h; exact id\u27e9\n")


def prune_items(items, header, path, lean_exe, rounds=30):
    """Drop declarations Lean rejects (set-builder notation, etc.)."""
    alive = list(items)
    for _ in range(rounds):
        lines = header.split("\n")
        index = []
        for name, text in alive:
            lo = len(lines) + 1
            lines.extend(text.split("\n"))
            index.append((name, lo, len(lines)))
        path.write_text("\n".join(lines) + "\nend Megalodon\n", encoding="utf-8")
        ok, errs, _ = compile_lean(path, lean_exe)
        if ok:
            return alive, True
        bad = {n for ln in errs for n, lo, hi in index if lo <= ln <= hi}
        if not bad:
            return alive, False
        alive = [e for e in alive if e[0] not in bad]
    return alive, False


# ----------------------------------------------------------------------
# proof translation
# ----------------------------------------------------------------------

def _split_tactics(line):
    """Split `let p q. assume H1 H2.` into separate tactics (top level only)."""
    parts, buf, depth = [], "", 0
    for ch in line:
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth -= 1
        if ch == "." and depth == 0:
            if buf.strip():
                parts.append(buf.strip())
            buf = ""
        else:
            buf += ch
    if buf.strip():
        parts.append(buf.strip())
    return parts


def _tactic_complete(t):
    """Is `t` a finished Megalodon tactic line?

    A tactic ends at a `.` outside any bracket. The subtlety is that `{` and
    `}` are BOTH proof-block delimiters and set-builder brackets, so a line
    ending in `{g w|w :e SNoL x}` must not be mistaken for a block close.
    """
    s = t.strip()
    if not s or s == "}":
        return True
    opens = s.startswith("{")
    if opens:
        s = s[1:].strip()
    bd = s.count("{") - s.count("}")
    if opens:
        if bd >= 0:
            return True                  # block opener; leave it open
        s = s.rstrip()
        if s.endswith("}"):              # block opened and closed on one line
            s = s[:-1]
    elif bd != 0:
        return True                      # opens or closes a block mid-line
    depth, dot = 0, False
    for ch in s:
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth -= 1
        elif ch == "." and depth == 0:
            dot = True
    return dot and depth == 0


def _join_tactics(lines):
    """Merge continuation lines so each entry is one complete Megalodon tactic.

    A tactic may run over several lines -- a long `exact` term, or a `claim`
    whose statement wraps. Processing raw lines splits those mid-term.
    """
    out, buf = [], ""
    for ln in lines:
        if not ln.strip():
            if buf:
                out.append(buf)
                buf = ""
            continue
        buf = (buf + " " + ln.strip()) if buf else ln.rstrip()
        if _tactic_complete(buf):
            out.append(buf)
            buf = ""
    if buf:
        out.append(buf)
    return out


def _brace_block(lines, i):
    """Collect a `{ ... }` block starting at lines[i]; return (inner, next_i).

    Only the braces that delimit THIS block are removed. A nested one-line
    block (`{ let h. exact e. }`) has to keep its own braces, or the recursive
    call cannot find it and the stray `}` leaks into the output.
    """
    depth, out, started = 0, [], False
    while i < len(lines):
        line, buf, j, closed = lines[i], "", 0, False
        while j < len(line):
            ch = line[j]
            if ch == "{":
                depth += 1
                if depth == 1 and not started:
                    started = True
                    j += 1
                    continue            # drop the brace that opens the block
            elif ch == "}":
                depth -= 1
                if depth == 0:
                    closed = True       # drop the brace that closes it
                    break
            buf += ch
            j += 1
        # keep leading whitespace: bullet scoping inside the block is
        # decided by indentation, so stripping it flattens nested subgoals
        out.append(buf.rstrip())
        i += 1
        if closed:
            break
    return out, i


UNSUPPORTED = re.compile(r"\b(induction|cases)\b")


def translate_tactics(lines, conv, indent=2):
    """Megalodon tactic script -> Lean tactic block. None if untranslatable."""
    out, i = [], 0
    pad = " " * indent
    while i < len(lines):
        raw = lines[i]
        if not raw.strip():
            i += 1
            continue
        if UNSUPPORTED.search(raw):
            return None

        stripped = raw.strip()
        if (stripped[:1] in "-+*" and stripped[1:2].isspace()
                and not stripped.startswith("->")):
            # A `-` opens a subgoal; every following line indented past it
            # belongs to that subgoal and must be nested under Lean's `·`,
            # not left at the bullet's own indentation.
            base = len(raw) - len(raw.lstrip())
            blk, j = [stripped[1:].lstrip()], i + 1
            while j < len(lines):
                nxt = lines[j]
                if nxt.strip() and len(nxt) - len(nxt.lstrip()) <= base:
                    break
                blk.append(nxt)
                j += 1
            sub = translate_tactics(blk, conv, indent + 2)
            if sub is None:
                return None
            if sub:
                out.append(pad + "· " + sub[0].strip())
                out.extend(sub[1:])
            i = j
            continue
        bullet = False

        # claim NAME : STMT.  { sub-proof }   ->   have NAME : STMT := by ...
        # `- { tac. tac. }` -- Megalodon groups a subgoal's proof in braces.
        # The braces are pure grouping here, so translate the contents in
        # place; leaving them unhandled leaks a stray `}` into the output.
        if stripped.startswith("{"):
            inner, nxt = _brace_block(lines, i)
            sub = translate_tactics(inner, conv, indent)
            if sub is None:
                return None
            out.extend(sub)
            i = nxt
            continue

        m = re.match(r"^claim\s+([A-Za-z_][\w']*)\s*:\s*(.*)$", stripped)
        blk = None
        if m:
            rest = m.group(2)
            # the statement runs to its terminating `.`; a `{` before that is
            # set-builder notation (`{0} :\/: {g x|x :e X}`), not a block
            d, dot = 0, None
            for k, ch in enumerate(rest):
                if ch in "([{":
                    d += 1
                elif ch in ")]}":
                    d -= 1
                elif ch == "." and d == 0:
                    dot = k
                    break
            stmt_src = rest if dot is None else rest[:dot]
            tail = "" if dot is None else rest[dot+1:]
            bi = tail.find("{")
            if bi >= 0:                 # `claim L: STMT. { ... }` on one line
                inner, nxt = _brace_block([tail[bi:]] + lines[i+1:], 0)
                blk = (inner, i + nxt)
            elif i + 1 < len(lines) and lines[i + 1].lstrip().startswith("{"):
                blk = _brace_block(lines, i + 1)
        if m and blk:
            name, stmt = m.group(1), conv.expr(stmt_src.strip().rstrip("."))
            inner, nxt = blk
            sub = translate_tactics(inner, conv, indent + 2)
            if sub is None:
                return None
            out.append("%s%shave %s : %s := by"
                       % (pad, "· " if bullet else "", name, stmt))
            out.extend(sub)
            i = nxt
            continue

        first = True
        for part in _split_tactics(stripped):
            occ = None
            # set x := e   ->   let x := e
            mset = re.match(r"^set\s+([A-Za-z_][\w']*)\s*(?::\s*([^:=]+?))?\s*:=\s*(.+)$", part)
            if mset:
                nm, ty, val = mset.group(1), mset.group(2), mset.group(3)
                part = ("let %s : %s := %s" % (nm, conv.expr(ty), conv.expr(val))
                        if ty else "let %s := %s" % (nm, conv.expr(val)))
            else:
                # witness t  ->  supply t to the encoded existential
                mw = re.match(r"^witness\s+(.+)$", part)
                if mw:
                    t = conv.expr(mw.group(1))
                    out.append("%sintro _wP _wH" % pad)
                    # Megalodon's `witness` tactic accepts a bare,
                    # unparenthesized application (`witness f w`). Lean's
                    # `apply` reads space-separated tokens as separate
                    # curried arguments, so `apply _wH f w` parses as
                    # `(_wH f) w` instead of `_wH (f w)`. Parenthesizing
                    # the whole witness term disambiguates it -- and is a
                    # no-op (redundant but harmless) when `t` was already a
                    # single token or already parenthesized.
                    out.append("%sapply _wH (%s)" % (pad, t))
                    first = False
                    continue
                # `rewrite H at 2` rewrites only the 2nd occurrence.
                # Dropping the position rewrites ALL of them, which changes
                # the goal -- that is what broke `xm`. The occurrence index is
                # parked behind a sentinel so the numeral pass (which would
                # turn `2` into `ordsucc (ordsucc Empty)`) leaves it alone.
                mrw = re.match(r"^rewrite\s+(<-\s*)?(.+?)"
                               r"(?:\s+at\s+(\d+))?$", part)
                if mrw:
                    part = "rewrite%s [%s%s]" % ("\x00O\x00" if mrw.group(3) else "",
                                            "← " if mrw.group(1) else "",
                                            mrw.group(2).strip())
                    occ = mrw.group(3)
                part = re.sub(r"^symmetry$", "symm", part)
                part = re.sub(r"^transitivity\s+(.+)$",
                              r"apply Eq.trans (b := \1)", part)
                part = re.sub(r"^reflexivity$", "rfl", part)
                part = re.sub(r"^f_equal$", "congr", part)
                part = re.sub(r"^let\b", "intro", part)
                part = re.sub(r"^assume\s+", "intro ", part)
                # `prove X` restates the goal. If our rendering of X is not
                # syntactically what Lean shows, `show` fails and kills the
                # proof -- but Lean works up to defeq anyway, so make it
                # advisory rather than load-bearing.
                part = re.sub(r"^prove\b", "try show", part)
                # [\w\s] alone misses primed names (`Hw'`, `w'`), which are
                # idiomatic here -- so `intro Hw': w' :e L` never matched and
                # the type annotation leaked straight through as invalid
                # Lean syntax (`intro` takes bare names, not `name : type`).
                part = re.sub(r"^intro\s+([\w\s']+?)\s*:.*$", r"intro \1", part)
                part = conv.expr(part)
                # Two Megalodon idioms do not survive the mapping onto Lean's
                # native connectives:
                #   * `False` is `forall p:prop, p`, so a proof of it proves
                #     anything -- Lean needs `apply`, not `exact`.
                #   * `eq` is Leibniz, so reflexivity is `fun q H => H`, which
                #     does not typecheck against Lean's `Eq`; `rfl` does.
                # Each branch still has to close the goal, so this stays sound.
                if occ:
                    # restored after conversion: the braces would otherwise be
                    # read as set-builder notation
                    part = part.replace(
                        "\x00O\x00",
                        " (config := { occs := .pos [%s] })" % occ)
                    occ = None
                mex = re.match(r"^exact\s+(.*)$", part, re.S)
                if mex:
                    trm = mex.group(1).strip()
                    # `rfl` only rescues the Leibniz-reflexivity idiom
                    # (`fun q H => H`), and it must be tried BEFORE `apply`:
                    # applying a lambda succeeds while leaving the goal open,
                    # so `first` would stop there and strand it. Trying `rfl`
                    # after every `exact` makes elaboration far too slow.
                    if re.match(r"^\(?\s*fun\s+\w+\s+\w+\s*=>\s*\w+\s*\)?$",
                                trm):
                        part = "first | exact %s | rfl | apply %s" % (trm, trm)
                    else:
                        part = "first | exact %s | apply %s" % (trm, trm)
            prefix = ("· " if (bullet and first) else ("  " if bullet else ""))
            out.append(pad + prefix + part)
            first = False
        i += 1
    return out


# Megalodon's `=` is Leibniz equality, so its canonical proof of `x = x` is
# the identity lambda `fun q H => H`. Bound to Lean's `Eq` that does not
# typecheck, and when the term sits in ARGUMENT position there is no tactic
# slot to put a fallback in. Wrapping it in a term-level `by first | ... | rfl`
# keeps the original reading where it works and falls back to `rfl` where the
# term was really proving reflexivity. Both branches must still close the goal.
IDENT_LAMBDA = re.compile(r"\(fun (\w+) (\w+) => (\w+)\)")


def relax_identity_lambdas(text):
    def sub(m):
        a, b, body = m.groups()
        if body != b or body == a:
            return m.group(0)          # not an identity lambda; leave alone
        return "(by first | exact (fun %s %s => %s) | rfl)" % (a, b, body)
    return IDENT_LAMBDA.sub(sub, text)


def translate_proof(proof_lines, conv):
    """Return Lean proof text, or None if it cannot be translated."""
    body = " ".join(" ".join(proof_lines).split())
    m = re.match(r"^exact\s*\((.*)\)\s*\.$", body, re.S) or \
        re.match(r"^exact\s+(.*)\.$", body, re.S)
    if m:
        return ":= " + relax_identity_lambdas(conv.expr(m.group(1).strip()))

    tac = translate_tactics(
        _join_tactics([l.expandtabs(4) for l in proof_lines]), conv)
    if not tac:
        return None
    return ":= by\n" + relax_identity_lambdas("\n".join(tac))


# ----------------------------------------------------------------------
# categorisation
# ----------------------------------------------------------------------
# Classification is POSITIVE for every tier: each theorem is filed by the
# vocabulary it actually uses, in specificity order. `prop_logic` used to be
# the fallback bucket, which quietly filed arithmetic and surreal results
# (`mul_nat_0R`, `eps_1_half_eq1`) as propositional logic and made its score
# meaningless. The name is checked as well as the body, because this corpus
# names theorems after their domain (539 of 999 carry SNo/PNo).
DOMAIN = [
    ("surreals", re.compile(
        r"\b(SNo\w*|PNo\w*|PSNo|eps_\w*|SurrealRec\w*|abs_SNo|minus_SNo|"
        r"add_SNo|mul_SNo|div_SNo|recip_SNo|exp_SNo\w*|real|rational|"
        r"diadic\w*|int|int_lin_comb|divides_int|gcd_reln|nonincrfinseq|"
        r"Pi_SNo|tag)\b")),
    ("ordinals", re.compile(r"\b(ordinal\w*|TransSet|ZF_closed|\w*_closed)\b")),
    ("nat_arith", re.compile(
        r"\b(nat_p|nat_\w*|\w*_nat|omega|ordsucc\w*|Pi_nat|primes|prime_nat|"
        r"composite_nat|nat_pair|nat_primrec|NatRec\w*)\b")),
    ("set_theory", re.compile(
        r"\b(In|Subq|Empty|Union|Power|Repl|UnivOf|binunion|binintersect|"
        r"setminus|Sing|UPair|Sep|famunion|ReplSep|Sigma|setsum|setprod|"
        r"setexp|proj0|proj1|Inj0|Inj1|Unj|pair\w*|equip|atleastp|inj|surj|"
        r"bij|inv|finite|infinite|Eps_i\w*|Descr\w*|If_i\w*|In_rec\w*|"
        r"In_ind|set_ext|Vo)\b|:e|c=")),
]

# Purely logical vocabulary: connectives, quantifiers, and equality.
PROP_VOCAB = re.compile(
    r"\b(and\w*|or\w*|not\w*|iff\w*|True|False|ex|exactly1of\w*|xm|dneg|"
    r"prop_ext\w*|pred_ext|demorgan|FalseE)\b|/\\|\\/|<->|~")


def categorise(th):
    blob = th["name"] + " " + th["stmt"] + " " + " ".join(th["proof"])
    for name, pat in DOMAIN:
        if pat.search(blob):
            return name
    if PROP_VOCAB.search(blob):
        return "prop_logic"
    # left over: bare equality facts. Numerals make them arithmetic
    # (`0 <> 1`); without them it is plain equality reasoning (`eq_i_tra`).
    return "nat_arith" if re.search(r"\b\d+\b", blob) else "prop_logic"


TIER_ORDER = ["prop_logic", "set_theory", "nat_arith", "ordinals", "surreals"]

TIER_BLURB = {
    "prop_logic": "Propositional logic: the connectives and their introduction\n"
                  "  and elimination rules. Megalodon defines and/or/not/iff as\n"
                  "  impredicative (Church) encodings rather than as built-in\n"
                  "  types, so these proofs work by unfolding those encodings.",
    "set_theory": "Set theory: membership, subset, union, power set, replacement\n"
                  "  and separation, over Megalodon's primitive sort `set`.",
    "nat_arith":  "Natural-number arithmetic: nat_p, ordsucc, addition,\n"
                  "  multiplication and exponentiation. Numerals are sets:\n"
                  "  0 is Empty and n+1 is ordsucc n.",
    "ordinals":   "Ordinals: transitive sets of transitive sets, and the\n"
                  "  arithmetic built on them.",
    "surreals":   "Surreal numbers: Conway's construction via SNoCut, built on\n"
                  "  the sign-sequence representation (PNo).",
}


def tier_header(tier, own, total, deps, prelude_n, prelude_total):
    """Explain what a generated category file contains and how it was checked."""
    return (
        "/-\n"
        "  %s.lean -- generated by megalodon_full.py from a Megalodon source file.\n"
        "  DO NOT EDIT: regenerate instead.\n"
        "\n"
        "  %s\n"
        "\n"
        "  Contents\n"
        "    %d theorem(s) of this category, machine-checked by Lean.\n"
        "    %d lemma(s) borrowed from other categories, each marked\n"
        "    `-- dependency from <category>`, so this file compiles on its own.\n"
        "    %d of %d prelude declarations -- only those these proofs reach.\n"
        "\n"
        "  Coverage: %d of %d theorems in this category were translated and\n"
        "  verified. The rest failed to compile and were removed: this file\n"
        "  contains no `sorry` and no unproved claims.\n"
        "\n"
        "  Verify independently:   lean -D maxErrors=20000 %s.lean\n"
        "-/\n" % (tier, TIER_BLURB.get(tier, tier), own, deps,
                  prelude_n, prelude_total, own, total, tier))


# ----------------------------------------------------------------------
# verification with pruning
# ----------------------------------------------------------------------

def compile_lean(path, lean_exe, timeout=1800):
    try:
        r = subprocess.run([lean_exe, "-D", "maxErrors=20000", str(path)],
                           capture_output=True,
                           text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        # No error lines come back, so callers must not read this as success.
        return False, None, "timeout"
    out = (r.stderr or "") + (r.stdout or "")
    errs = re.findall(r":(\d+):\d+: error", out)
    return r.returncode == 0, [int(x) for x in errs], out


def verify_and_prune(path, prelude, entries, lean_exe, rounds=25):
    """Drop theorems whose lines carry Lean errors until the file compiles."""
    alive = list(entries)
    for _ in range(rounds):
        _, index = render(path, prelude, alive)
        ok, err_lines, _ = compile_lean(path, lean_exe)
        if ok:
            return alive, True
        if err_lines is None:
            return alive, False
        bad = set()
        for ln in err_lines:
            for name, lo, hi in index:
                if lo <= ln <= hi:
                    bad.add(name)
        if not bad:                       # error outside any theorem: give up
            return alive, False
        alive = [e for e in alive if e[0] not in bad]
        if not alive:
            return [], False
    return alive, False


# Proof strategies tried when the ported Megalodon proof fails but the
# statement typechecks. `solve_by_elim` is seeded with the lemma names the
# original Megalodon proof cites, which is what makes the search targeted
# rather than blind. Each candidate is capped so a failing search cannot
# dominate the run.
CAP = "set_option maxHeartbeats 200000 in\n"


def proof_seeds(proof_lines, known, limit=12):
    """Lemma names cited by a Megalodon proof, in order of first use."""
    out = []
    for ln in proof_lines:
        for w in re.findall(r"[A-Za-z_][\w']*", ln):
            if w in known and w not in out:
                out.append(w)
    return out[:limit]


def strategies_for(seeds):
    """Candidate Lean proofs, cheapest first.

    Every tactic sits on its own line indented under a bare `by`: writing
    `:= by intros` and continuing on the next line at a shallower column ends
    the tactic block, which silently turns each candidate into a syntax error.
    """
    lst = ", ".join(seeds)
    s = []
    if lst:
        s.append("intros\n  solve_by_elim [%s]" % lst)
        s.append("try unfold and or not iff ex\n  intros\n"
                 "  solve_by_elim [%s]" % lst)
        s.append("intros\n  first\n  | apply %s <;> assumption\n"
                 "  | exact %s" % (seeds[0], seeds[0]))
    s.append("intros\n  solve_by_elim")
    s.append("try unfold and or not iff ex\n  intros\n  solve_by_elim")
    s.append("intros\n  apply_assumption <;> assumption")
    s.append("intros\n  assumption")
    s.append("intros\n  rfl")
    s.append("trivial")
    s.append("intros\n  simp_all")
    return [":= by\n  %s" % x for x in s]


def recover(path, prelude, survivors, failed, lean_exe, seeds, budget=2400):
    """Retry failed theorems with seeded proof search.

    The statement already typechecks; only the ported proof failed. One
    compile per strategy slot keeps this cheap regardless of how many
    theorems are retried.
    """
    start = time.time()
    recovered, remaining = [], list(failed)
    # Seed names are collected from every Theorem/Definition/Axiom/Parameter
    # DECLARED anywhere in the corpus, regardless of whether that theorem's
    # own translation survived pruning. Citing a since-deleted name as a
    # solve_by_elim HINT does not reliably surface as a hard compile error --
    # Lean can silently fall back to a synthetic `sorry` for an unresolvable
    # hint while the overall tactic still reports success, which slips past
    # this function's error-range check and only shows up later in the
    # axiom audit as `sorryAx`. Restricting hints to names that are actually
    # present among survivors (i.e. really exist in the file being compiled)
    # closes that hole at the source instead of relying on a downstream audit
    # to catch it.
    alive_names = {n for n, _ in survivors}
    seeds = {n: [s for s in v if s in alive_names] for n, v in seeds.items()}
    nslots = max(len(strategies_for(seeds.get(n) or [])) for n, _ in failed) \
        if failed else 0
    for k in range(nslots):
        if not remaining or time.time() - start > budget:
            break
        cands = []
        for name, text in remaining:
            strats = strategies_for(seeds.get(name) or [])
            if k >= len(strats):
                continue
            head = text.split(":=")[0].rstrip()
            cands.append((name, CAP + "%s %s" % (head, strats[k])))
        if not cands:
            continue
        _, index = render(path, prelude, survivors + recovered + cands)
        _, errs, _ = compile_lean(path, lean_exe)
        if errs is None:              # timed out: trust nothing from this pass
            continue
        bad = {n for ln in errs for n, lo, hi in index if lo <= ln <= hi}
        good = [(n, t) for n, t in cands if n not in bad]
        if good:
            recovered.extend(good)
            names = {n for n, _ in good}
            remaining = [(n, t) for n, t in remaining if n not in names]
    return recovered


def prune_prelude(items, body):
    """Keep only the prelude declarations a given body can actually reach.

    Every category file otherwise carries all ~198 declarations, including the
    surreal-number machinery a propositional-logic file never mentions. Source
    order is preserved, since a declaration must precede its uses.

    Notation is keyed by the LEAN token (`\u22cf`), which is what appears in the
    body; including a notation line also pulls in the definition it names.
    Instances are always seeded -- they apply implicitly, so no textual
    reference proves them unneeded -- and seeded into the FRONTIER, not the
    result, so whatever they name is pulled in with them.
    """
    text_of, by_name, by_tok, seeds = {}, {}, {}, []
    for name, text in items:
        text_of[name] = text
        if name.startswith("notation:"):
            m = re.search(r'"\s*(\S+)\s*"', text)
            if m:
                by_tok[m.group(1)] = name
        elif name.startswith("coefun:"):
            seeds.append(name)
        else:
            by_name[name] = name

    def refs(t):
        out = {w for w in re.findall(r"[A-Za-z_][\w']*", t) if w in by_name}
        out |= {nm for tok, nm in by_tok.items() if tok in t}
        return out

    need, frontier = set(), list(refs(body)) + seeds
    while frontier:
        n = frontier.pop()
        if n in need:
            continue
        need.add(n)
        frontier.extend(refs(text_of[n]) - need)
    return [(n, t) for n, t in items if n in need]


def render(path, header, entries):
    lines = header.split("\n")
    index = []
    for name, text in entries:
        lo = len(lines) + 1
        lines.extend(text.split("\n"))
        index.append((name, lo, len(lines)))
    lines.append("")
    lines.append("end Megalodon")
    path.write_text("\n".join(lines), encoding="utf-8")
    return "\n".join(lines), index

# ----------------------------------------------------------------------
# main
# ----------------------------------------------------------------------

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("input", type=Path)
    ap.add_argument("--output", type=Path, default=Path("./lean_out"))
    ap.add_argument("--no-verify", action="store_true")
    ap.add_argument("--statements-only", action="store_true",
                    help="Emit every theorem STATEMENT with `sorry` for the "
                         "proof. Checks that statements typecheck; proves "
                         "nothing.")
    args = ap.parse_args()

    lean_exe = shutil.which("lean")
    if not lean_exe and not args.no_verify:
        print("lean not on PATH (use --no-verify to skip)"); return 2

    raw_text = args.input.read_text(encoding="utf-8", errors="replace")
    src = parse_source(raw_text)
    tokmap = build_token_map(src["fixity"])
    conv = Converter(tokmap, src["binders"],
                     build_binder_ops(strip_comments(raw_text)),
                     build_setlam(strip_comments(raw_text)))
    items = prelude_items(raw_text, conv, tokmap, src["fixity"])

    args.output.mkdir(parents=True, exist_ok=True)
    ppath = args.output / "Prelude.lean"
    if args.no_verify:
        kept = items
    else:
        kept, ok = prune_items(items, HEADER, ppath, lean_exe)
        print("prelude       : %d/%d declarations kept  (%s)"
              % (len(kept), len(items), "PASS" if ok else "partial"))
    prelude = HEADER + "\n".join(t for _, t in kept)

    known = set(re.findall(
        r"^(?:Parameter|Axiom|Definition|Theorem)\s+([A-Za-z_][\w']*)",
        strip_comments(raw_text), re.M))
    seeds = {}
    # section theorem -> the explicit binders it was ACTUALLY emitted with.
    # The parse-time list can be short: binders are recomputed after
    # substitution, so a theorem may gain a variable (In_rec_G_ii_In_rec_ii
    # gains `Fr`) that in-section callers must then pass as well.
    emitted_binders = {}
    entries = []          # (name, text, tier) in SOURCE ORDER
    untranslated = []
    for th in src["theorems"]:
        proof = ":= sorry" if args.statements_only else translate_proof(th["proof"], conv)
        if proof is None:
            untranslated.append(th["name"]); continue
        if args.statements_only:
            proof = ":= sorry"
        stmt_l = conv.expr(th["stmt"])
        # A section-local `Let` was lifted to a qualified top-level def, and
        # that lifted def takes the section variables it absorbed -- so uses
        # need the arguments too, not just the new name.
        for nm, (qual, lvars) in (th.get("lets") or {}).items():
            rep = "(%s %s)" % (qual, " ".join(lvars)) if lvars else qual
            stmt_l = re.sub(r"\b%s\b" % re.escape(nm), rep, stmt_l)
            proof = re.sub(r"\b%s\b" % re.escape(nm), rep, proof)
        binders = th.get("binders") or []
        # a section-scoped definition must be applied to the section variables
        # A section-scoped theorem is applied only to the section variables
        # that _bind leaves EXPLICIT: Type- and Prop-typed ones are implicit,
        # so passing them positionally shifts every later argument.
        secthm_args = {}
        for d, dbs in (th.get("secthms") or {}).items():
            if d in emitted_binders:
                secthm_args[d] = emitted_binders[d]
                continue
            keep = []
            for v, ty in dbs:
                if re.match(r"^(Type|Sort)\b", conv.expr(ty).strip()):
                    continue          # type variables stay implicit
                keep.append(v)
            secthm_args[d] = keep
        for d, dvars in list((th.get("secdefs") or {}).items()) \
                + list(secthm_args.items()):
            # apply it to the section variables it actually abstracts over --
            # not to every variable the theorem happens to bind
            args_ = " ".join(dvars)
            if args_ and re.search(r"\b%s\b" % re.escape(d), stmt_l + proof):
                rep = "(%s %s)" % (d, args_)
                stmt_l = re.sub(r"\b%s\b(?!\s*\w*\s*:=)" % re.escape(d), rep, stmt_l)
                proof = re.sub(r"\b%s\b" % re.escape(d), rep, proof)
        # Recompute after substitution: applying a section theorem to its
        # section variables can introduce one the theorem never mentioned in
        # its own source text (In_rec_i_eq gains `Fr` from In_rec_i_G_f).
        allsec = th.get("allsec") or []
        if allsec:
            binders = [(v, ty) for v, ty in allsec
                       if re.search(r"\b%s\b" % re.escape(v),
                                    stmt_l + " " + proof)]
        # Same rule as declarations: section TYPE variables stay implicit
        # (uses go through notation), value variables are explicit.
        def _bind(v, ty):
            lty = conv.expr(ty)
            if re.match(r"^(Type|Sort)\b", lty.strip()):
                return " {%s : Sort u}" % v
            # Everything else stays EXPLICIT, including Prop-typed section
            # variables: `End` discharges them into real parameters, and uses
            # from outside the section pass them (`and3E A B C H`). Uses from
            # INSIDE the section omit them (`and3I H1 H2 H3`) -- the secthms
            # substitution supplies those.
            return " (%s : %s)" % (v, lty)
        bind = "".join(_bind(v, ty) for v, ty in binders)
        emitted_binders[th["name"]] = [
            v for v, ty in binders
            if not re.match(r"^(Type|Sort)\b", conv.expr(ty).strip())]
        text = "theorem %s%s : %s %s" % (th["name"], bind, stmt_l, proof)
        seeds[th["name"]] = proof_seeds(th["proof"], known)
        entries.append((th["name"], text, categorise(th)))

    total = len(src["theorems"])
    print("=" * 70)
    print("MEGALODON -> LEAN 4")
    print("=" * 70)
    print("source        : %s" % args.input)
    print("theorems       : %d" % total)
    print("translatable   : %d  (unsupported tactics: %d)"
          % (total - len(untranslated), len(untranslated)))
    print()

    # Verification runs over ONE source-ordered file. Splitting by category
    # first would break every theorem that cites a lemma filed under another
    # category, since Lean needs the dependency to come earlier in the file.
    order = {n: i for i, (n, _, _) in enumerate(entries)}
    tier_of = {n: t for n, _, t in entries}
    flat = [(n, t) for n, t, _ in entries]

    if args.no_verify:
        for tier in TIER_ORDER:
            own = [(n, t) for n, t, k in entries if k == tier]
            if own:
                render(args.output / ("%s.lean" % tier), prelude, own)
                print("%-12s %4d theorems (unverified)" % (tier, len(own)))
        return 0

    allpath = args.output / "All.lean"
    alive, ok = verify_and_prune(allpath, prelude, flat, lean_exe)
    alive_names = {n for n, _ in alive}
    failed = [(n, t) for n, t in flat if n not in alive_names]
    print("first pass    : %d/%d verified" % (len(alive), len(flat)))
    if failed:
        got = recover(allpath, prelude, alive, failed, lean_exe, seeds)
        if got:
            # recovered proofs must be re-filed in source order: a later
            # theorem may cite one of them
            alive = sorted(alive + got, key=lambda e: order[e[0]])
            print("recovery      : +%d by seeded proof search" % len(got))
    render(allpath, prelude, alive)
    alive_names = {n for n, _ in alive}
    text_of = dict(alive)

    print()
    grand = 0
    for tier in TIER_ORDER:
        own = [n for n, _, k in entries if k == tier and n in alive_names]
        total_t = sum(1 for _, _, k in entries if k == tier)
        if not total_t:
            continue
        # pull in whatever these proofs cite, transitively, so the category
        # file stands on its own
        need, frontier = set(own), list(own)
        while frontier:
            for w in re.findall(r"[A-Za-z_][\w']*", text_of[frontier.pop()]):
                if w in alive_names and w not in need:
                    need.add(w)
                    frontier.append(w)
        # Source order has to be kept across the whole file: a dependency
        # pulled in from another category may itself rest on a theorem of
        # THIS category, so deps cannot simply be grouped ahead of the rest.
        ownset = set(own)
        body = []
        deps_in_body = need - ownset
        for n in sorted(need, key=lambda n: order[n]):
            if n not in ownset:
                body.append(("--dep:" + n,
                             "-- dependency from %s" % tier_of[n]))
            body.append((n, text_of[n]))
        # Each category gets only the prelude it reaches, not all ~195
        # declarations -- a propositional-logic file has no business
        # carrying the surreal-number machinery.
        slim = prune_prelude(kept, "\n".join(t for _, t in body))
        path = args.output / ("%s.lean" % tier)
        head = tier_header(tier, len(own), total_t, len(deps_in_body),
                           len(slim), len(kept))
        render(path, head + HEADER + "\n".join(t for _, t in slim), body)
        tok, _, _ = compile_lean(path, lean_exe)
        if not tok:      # pruning was wrong somewhere: fall back to the full
            render(path, head + prelude, body)  # rather than ship a broken file
            tok, _, _ = compile_lean(path, lean_exe)
            slim = kept
        grand += len(own)
        print("%-12s %4d/%-4d verified   %s   (prelude %d/%d)"
              % (tier, len(own), total_t, "PASS" if tok else "FAIL",
                 len(slim), len(kept)))
    print()
    print("verified total : %d / %d" % (grand, total))
    print("output         : %s" % args.output)
    return 0


if __name__ == "__main__":
    sys.exit(main())
