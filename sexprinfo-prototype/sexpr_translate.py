#!/usr/bin/env python3
"""Proof-of-concept: translate Megalodon's -sexprinfo output (patched to
include PROOF entries, see pf_to_sexpr.patch) directly into Lean 4, using
proof TERMS rather than tactic scripts.

This is a first version, deliberately scoped to the non-polymorphic core
(no TLAM/TPAP/PTPAP/PTPLAM yet) to prove the architecture works end to end
before extending it. See sexprinfo-prototype/README.md for context.
"""
import sys, re

# ---------------------------------------------------------------- parsing
def parse_sexpr(text, i=0):
    """Parse one S-expression starting at i. Returns (node, next_i).
    A node is either a string atom or a list of nodes."""
    while text[i].isspace():
        i += 1
    if text[i] == '(':
        i += 1
        items = []
        while True:
            while text[i].isspace():
                i += 1
            if text[i] == ')':
                return items, i + 1
            node, i = parse_sexpr(text, i)
            items.append(node)
    elif text[i] == '"':
        j = i + 1
        buf = []
        while text[j] != '"':
            if text[j] == '\\':
                buf.append(text[j+1]); j += 2
            else:
                buf.append(text[j]); j += 1
        return "".join(buf), j + 1
    else:
        j = i
        while j < len(text) and not text[j].isspace() and text[j] not in "()":
            j += 1
        return text[i:j], j


def parse_toplevel_forms(text):
    """The sexprinfo output is one top-level form per line (mostly); parse
    each line independently, skipping non-form lines (WARNING:, etc.)."""
    forms = []
    for line in text.splitlines():
        line = line.strip()
        if not line.startswith("("):
            continue
        try:
            node, _ = parse_sexpr(line, 0)
        except Exception:
            continue
        forms.append(node)
    return forms


# ------------------------------------------------------------ translation
class Ctx:
    def __init__(self):
        self.hash_to_name = {}   # TMH hash -> Lean name (for tm-level DEF/AXIOM/PARAM/THM)
        self.prim_to_name = {}   # PRIM index -> Lean name
        self.tp_stack = []       # bound type-var names, outer to inner (TPVAR De Bruijn)
        self.tm_stack = []       # bound term-var names (DB De Bruijn)
        self.pf_stack = []       # bound proof-var names (Hyp De Bruijn)
        self.counter = 0

    def fresh(self, base):
        self.counter += 1
        return f"{base}{self.counter}"


def tp_to_lean(node, ctx):
    tag = node[0]
    if tag == "TPVAR":
        i = int(node[1])
        return ctx.tp_stack[-(i + 1)]
    if tag == "PROP":
        return "Prop"
    if tag == "SET":
        return "set"
    if tag == "AR":
        return f"({tp_to_lean(node[1], ctx)} -> {tp_to_lean(node[2], ctx)})"
    raise NotImplementedError(f"tp: {tag}")


def tm_to_lean(node, ctx):
    tag = node[0]
    if tag == "DB":
        i = int(node[1])
        return ctx.tm_stack[-(i + 1)]
    if tag == "TMH":
        h = node[1]
        if h not in ctx.hash_to_name:
            raise KeyError(f"unresolved TMH hash (forward or missing reference): {h}")
        return ctx.hash_to_name[h]
    if tag == "PRIM":
        i = int(node[1])
        return ctx.prim_to_name[i]
    if tag == "AP":
        return f"({tm_to_lean(node[1], ctx)} {tm_to_lean(node[2], ctx)})"
    if tag == "LAM":
        v = ctx.fresh("x")
        ty = tp_to_lean(node[1], ctx)
        ctx.tm_stack.append(v)
        body = tm_to_lean(node[2], ctx)
        ctx.tm_stack.pop()
        return f"(fun {v} : {ty} => {body})"
    if tag == "IMP":
        return f"({tm_to_lean(node[1], ctx)} -> {tm_to_lean(node[2], ctx)})"
    if tag == "ALL":
        v = ctx.fresh("x")
        ty = tp_to_lean(node[1], ctx)
        ctx.tm_stack.append(v)
        body = tm_to_lean(node[2], ctx)
        ctx.tm_stack.pop()
        return f"(forall {v} : {ty}, {body})"
    if tag == "TPAP":
        return f"({tm_to_lean(node[1], ctx)} {tp_to_lean(node[2], ctx)})"
    raise NotImplementedError(f"tm: {tag}")


def pf_to_lean(node, ctx):
    tag = node[0]
    if tag == "HYP":
        i = int(node[1])
        return ctx.pf_stack[-(i + 1)]
    if tag == "KNOWN":
        h = node[1]
        if h not in ctx.hash_to_name:
            raise KeyError(f"unresolved KNOWN hash: {h}")
        return ctx.hash_to_name[h]
    if tag == "PTMAP":
        return f"({pf_to_lean(node[1], ctx)} {tm_to_lean(node[2], ctx)})"
    if tag == "PPFAP":
        return f"({pf_to_lean(node[1], ctx)} {pf_to_lean(node[2], ctx)})"
    if tag == "PLAM":
        v = ctx.fresh("h")
        ty = tm_to_lean(node[1], ctx)  # the assumed proposition, itself a tm
        ctx.pf_stack.append(v)
        body = pf_to_lean(node[2], ctx)
        ctx.pf_stack.pop()
        return f"(fun {v} : {ty} => {body})"
    if tag == "TLAM":
        # NOT type-variable polymorphism (that's PTPLAM, separately). This is
        # an ordinary forall-introduction inside a proof -- e.g. andI's own
        # `forall P Q : Prop, ...` binders -- so it shares tm_stack/DB
        # numbering with the term side, not a fresh type-var stack.
        v = ctx.fresh("x")
        ty = tp_to_lean(node[1], ctx)
        ctx.tm_stack.append(v)
        body = pf_to_lean(node[2], ctx)
        ctx.tm_stack.pop()
        return f"(fun {v} : {ty} => {body})"
    if tag == "PTPLAM":
        # The genuine type-variable binder (matches the outer `i` count on
        # DEF/AXIOM/THM, when it appears explicitly in a proof term).
        v = ctx.fresh("T")
        ctx.tp_stack.append(v)
        body = pf_to_lean(node[1], ctx)
        ctx.tp_stack.pop()
        return f"(fun {v} : Type => {body})"
    if tag == "PTPAP":
        return f"({pf_to_lean(node[1], ctx)} {tp_to_lean(node[2], ctx)})"
    raise NotImplementedError(f"pf: {tag}")


def main():
    text = open(sys.argv[1], encoding="utf-8").read()
    forms = parse_toplevel_forms(text)
    ctx = Ctx()
    out = []
    thm_stmt = {}   # name -> translated Lean type, waiting for its PROOF
    ok, fail = 0, 0
    fail_examples = []

    def push_tpvars(i):
        """i-many polymorphic type parameters. Empirically verified against
        func_ext (2 type params): the FIRST nested type-application at a
        call site binds the parameter declared LAST in the Lean signature,
        not first -- so push in reverse, TPVAR 0 ending up as the first
        (outermost, leftmost) declared Lean parameter."""
        names = [ctx.fresh("T") for _ in range(i)]
        ctx.tp_stack.extend(reversed(names))
        return names

    def pop_tpvars(names):
        if names:
            del ctx.tp_stack[-len(names):]

    def implicit_prefix(names):
        # EXPLICIT, not implicit ({..}): Megalodon's own term structure
        # always instantiates a polymorphic type via an explicit TpAp/PTpAp
        # application node, never leaves it for inference. Using {..} here
        # made Lean read a later explicit `eq T18 x19` as supplying T18 for
        # eq's first VALUE argument, not its (implicit) type argument.
        return "".join(f"({n} : Type) " for n in names)

    for form in forms:
        tag = form[0]
        try:
            if tag == "PARAM":
                _, name, h, i, ty = form
                i = int(i)
                tvs = push_tpvars(i)
                lty = tp_to_lean(ty, ctx)
                pop_tpvars(tvs)
                out.append(f"axiom {name} {implicit_prefix(tvs)}: {lty}")
                ctx.hash_to_name[h] = name
            elif tag == "AXIOM":
                _, name, h, i, ty = form
                i = int(i)
                tvs = push_tpvars(i)
                lty = tm_to_lean(ty, ctx)
                pop_tpvars(tvs)
                out.append(f"axiom {name} {implicit_prefix(tvs)}: {lty}")
                ctx.hash_to_name[h] = name
            elif tag == "DEF":
                _, name, h, i, ty, tm = form
                i = int(i)
                tvs = push_tpvars(i)
                lty = tp_to_lean(ty, ctx)
                ltm = tm_to_lean(tm, ctx)
                pop_tpvars(tvs)
                out.append(f"noncomputable def {name} {implicit_prefix(tvs)}: {lty} := {ltm}")
                ctx.hash_to_name[h] = name
            elif tag == "PRIM":
                # Leading field is PRIM's own index (for later `Prim(i)`
                # references), NOT a polymorphism count -- PRIM has no
                # separate i field at all in the OCaml source's print.
                _, idx, name, h, ty = form
                lty = tp_to_lean(ty, ctx)
                out.append(f"axiom {name} : {lty}")
                ctx.hash_to_name[h] = name
                ctx.prim_to_name[int(idx)] = name
            elif tag == "THM":
                _, name, ahv, pfgahv, i, ty = form
                i = int(i)
                tvs = push_tpvars(i)
                lty = tm_to_lean(ty, ctx)
                pop_tpvars(tvs)
                thm_stmt[name] = (lty, ahv, tvs)
            elif tag == "PROOF":
                _, name, pf = form
                if name not in thm_stmt:
                    continue
                lty, ahv, tvs = thm_stmt[name]
                ctx.tp_stack.extend(tvs)
                lpf = pf_to_lean(pf, ctx)
                pop_tpvars(tvs)
                out.append(f"theorem {name} {implicit_prefix(tvs)}: {lty} := {lpf}")
                ctx.hash_to_name[ahv] = name
                ok += 1
        except Exception as e:
            fail += 1
            if len(fail_examples) < 15:
                fail_examples.append((tag, form[1] if len(form) > 1 else "?", str(e)[:120]))
            continue

    print(f"translated OK: {ok}  failed: {fail}")
    for t, n, e in fail_examples:
        print(f"  FAIL {t} {n}: {e}")

    with open(sys.argv[2], "w", encoding="utf-8") as f:
        # `set` is a base sort of Megalodon's own foundation (like Prop),
        # never declared within the theory itself, so the export never
        # emits it -- must be seeded by hand, same as the tactic-based
        # translator's prelude does.
        # The namespace wrapper is not cosmetic: Megalodon's own `True`/
        # `False`/etc. definitions would otherwise collide with Lean's
        # built-in root-level ones of the same name.
        f.write("set_option maxRecDepth 8000\n\n")
        f.write("namespace Megalodon\n\n")
        f.write("axiom set : Type\n\n")
        f.write("\n".join(out))
        f.write("\n\nend Megalodon\n")


if __name__ == "__main__":
    main()
