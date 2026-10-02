#!/usr/bin/env python3
"""Translate Megalodon's -sexprinfo output (patched to include PROOF
entries, see pf_to_sexpr.patch) directly into Lean 4, using proof TERMS
rather than tactic scripts. Verified 999/999 on the 100thms_12.mg
reference corpus -- see sexprinfo-prototype/README.md.

Usage:
    python3 sexpr_translate.py <input.sexpr> <output_dir>

Writes <output_dir>/All.lean (everything, authoritative) plus five
per-category files (prop_logic / set_theory / nat_arith / ordinals /
surreals), each including only the prelude items and cross-category
theorems it actually depends on, so each is intended to compile
standalone.
"""
import sys, re, os

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


# --------------------------------------------------------- categorisation
# Same vocabulary heuristic as megalodon_full.py's DOMAIN/PROP_VOCAB/
# categorise, so category boundaries match the tactic-based translator's.
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
PROP_VOCAB = re.compile(
    r"\b(and\w*|or\w*|not\w*|iff\w*|True|False|ex|exactly1of\w*|xm|dneg|"
    r"prop_ext\w*|pred_ext|demorgan|FalseE)\b|/\\|\\/|<->|~")
TIER_ORDER = ["prop_logic", "set_theory", "nat_arith", "ordinals", "surreals"]


def categorise(name, type_text, cited_names):
    blob = name + " " + type_text + " " + " ".join(cited_names)
    for cat, pat in DOMAIN:
        if pat.search(blob):
            return cat
    if PROP_VOCAB.search(blob):
        return "prop_logic"
    return "nat_arith" if re.search(r"\b\d+\b", blob) else "prop_logic"


# ------------------------------------------------------------ translation
class Ctx:
    def __init__(self):
        # Two maps, not one. Megalodon hashes objects and propositions in
        # separate namespaces, and the same hash can legitimately appear in
        # both: `True` is a DEF whose hash denotes the term
        # `forall p, p -> p`, and `TrueI` is a THM whose hash denotes the
        # proposition `True` -- the same hash. A `TMH` in a term has to
        # resolve to `True` and a `KNOWN` in a proof to `TrueI`, so one
        # map cannot serve both: whichever declaration came last would
        # win and the other reference would get the wrong name.
        self.tm_hash_to_name = {}   # TMH hash   -> Lean name (PARAM/DEF/PRIM)
        self.pf_hash_to_name = {}   # KNOWN hash -> Lean name (AXIOM/THM)
        self.prim_to_name = {}      # PRIM index -> Lean name
        self.tp_stack = []       # bound type-var names (TPVAR De Bruijn)
        self.tm_stack = []       # bound term-var names (DB De Bruijn)
        self.pf_stack = []       # bound proof-var names (Hyp De Bruijn)
        self.counter = 0
        self.current_deps = None  # set(), collected while translating one entry

    def fresh(self, base):
        self.counter += 1
        return f"{base}{self.counter}"

    def resolve_hash(self, h, kind):
        """`kind` is 'tm' for a TMH (an object) or 'pf' for a KNOWN (a
        fact). They are different namespaces; see Ctx.__init__."""
        table = self.tm_hash_to_name if kind == "tm" else self.pf_hash_to_name
        if h not in table:
            other = self.pf_hash_to_name if kind == "tm" else self.tm_hash_to_name
            hint = (" (it is registered as a %s, not a %s -- the two "
                    "namespaces must not be mixed)"
                    % ("fact" if kind == "tm" else "object",
                       "object" if kind == "tm" else "fact")) \
                if h in other else ""
            raise KeyError("unresolved %s hash: %s%s" % (kind.upper(), h, hint))
        name = table[h]
        if self.current_deps is not None:
            self.current_deps.add(name)
        return name

    def resolve_prim(self, i):
        name = self.prim_to_name[i]
        if self.current_deps is not None:
            self.current_deps.add(name)
        return name


def tp_to_lean(node, ctx):
    tag = node[0]
    if tag == "TPVAR":
        return ctx.tp_stack[-(int(node[1]) + 1)]
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
        return ctx.tm_stack[-(int(node[1]) + 1)]
    if tag == "TMH":
        h = node[1]
        return ctx.resolve_hash(h, "tm")
    if tag == "PRIM":
        return ctx.resolve_prim(int(node[1]))
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


def _has_redex(node):
    """True if `node` contains a beta-redex: an AP whose function is a LAM.

    Lean's elaborator beta-reduces a `fun`'s *type annotation* during
    elaboration, but leaves redexes alone everywhere else -- including in
    a theorem's stated type, and in a binder type it infers from the
    expected type rather than reading from an annotation. Megalodon does
    record such redexes (a PLAM's proposition is often an un-reduced
    `(AP (LAM (SET) P) y)`), and its content hash is taken over the
    un-reduced term, so an annotation here would silently change the
    hash. Such binders are therefore emitted unannotated. See
    `reverse_translate.py` for the check that this round-trips.
    """
    if not isinstance(node, list):
        return False
    if node[0] == "AP" and isinstance(node[1], list) and node[1][0] == "LAM":
        return True
    return any(_has_redex(c) for c in node[1:])


def pf_to_lean(node, ctx):
    tag = node[0]
    if tag == "HYP":
        return ctx.pf_stack[-(int(node[1]) + 1)]
    if tag == "KNOWN":
        h = node[1]
        return ctx.resolve_hash(h, "pf")
    if tag == "PTMAP":
        return f"({pf_to_lean(node[1], ctx)} {tm_to_lean(node[2], ctx)})"
    if tag == "PPFAP":
        return f"({pf_to_lean(node[1], ctx)} {pf_to_lean(node[2], ctx)})"
    if tag == "PLAM":
        v = ctx.fresh("h")
        # Translate the proposition either way: it is what records this
        # proof's dependencies on earlier facts, which the per-category
        # output files need even when the annotation itself is dropped.
        ty = tm_to_lean(node[1], ctx)
        ctx.pf_stack.append(v)
        body = pf_to_lean(node[2], ctx)
        ctx.pf_stack.pop()
        if _has_redex(node[1]):
            # Wrapped, so the proposition is an argument rather than an
            # annotation and Lean leaves it exactly as Megalodon wrote it.
            return f"(fun {v} : (mgProp {ty}) => {body})"
        return f"(fun {v} : {ty} => {body})"
    if tag == "TLAM":
        # NOT type-variable polymorphism (that's PTPLAM). An ordinary
        # forall-introduction inside a proof -- shares tm_stack/DB
        # numbering with the term side.
        v = ctx.fresh("x")
        ty = tp_to_lean(node[1], ctx)
        ctx.tm_stack.append(v)
        body = pf_to_lean(node[2], ctx)
        ctx.tm_stack.pop()
        return f"(fun {v} : {ty} => {body})"
    if tag == "PTPLAM":
        v = ctx.fresh("T")
        ctx.tp_stack.append(v)
        body = pf_to_lean(node[1], ctx)
        ctx.tp_stack.pop()
        return f"(fun {v} : Type => {body})"
    if tag == "PTPAP":
        return f"({pf_to_lean(node[1], ctx)} {tp_to_lean(node[2], ctx)})"
    raise NotImplementedError(f"pf: {tag}")


# ------------------------------------------------- beta-eta normalisation
# Megalodon's content hash is taken over the beta-eta normal form:
# `Syntax.tm_id` is `hashval_hexstring (tm_hashroot (... (tm_beta_eta_exeq_norm m)))`.
# So two declarations sharing a hash are guaranteed to be beta-eta equal,
# NOT to be structurally identical -- `coarser_than := fun A B => Subq A B`
# shares `Subq`'s hash while being its eta-expansion. Any check against
# those hashes therefore has to normalise, or it reports false mismatches
# on perfectly consistent input.
#
# In the term language only LAM and ALL bind a DB variable; AP, IMP and
# TPAP bind nothing and so do not shift indices.

_BINDS_DB = ("LAM", "ALL")


def _shift(e, d, cutoff=0):
    if not isinstance(e, list):
        return e
    if e[0] == "DB":
        i = int(e[1])
        return ["DB", str(i + d)] if i >= cutoff else e
    if e[0] in _BINDS_DB:
        return [e[0], _shift(e[1], d, cutoff), _shift(e[2], d, cutoff + 1)]
    return [e[0]] + [_shift(c, d, cutoff) for c in e[1:]]


def _subst(e, k, v):
    """Replace DB k by v; free DB above k shift down to fill the gap."""
    if not isinstance(e, list):
        return e
    if e[0] == "DB":
        i = int(e[1])
        if i == k:
            return _shift(v, k)
        return ["DB", str(i - 1)] if i > k else e
    if e[0] in _BINDS_DB:
        return [e[0], _subst(e[1], k, v), _subst(e[2], k + 1, v)]
    return [e[0]] + [_subst(c, k, v) for c in e[1:]]


def _occurs(e, k):
    """Does DB k occur free in e?"""
    if not isinstance(e, list):
        return False
    if e[0] == "DB":
        return int(e[1]) == k
    if e[0] in _BINDS_DB:
        return _occurs(e[1], k) or _occurs(e[2], k + 1)
    return any(_occurs(c, k) for c in e[1:])


# The third component of Megalodon's normaliser (the "exeq" in
# `tm_beta_eta_exeq_norm`): the polymorphic constants `ex`, `eq` and `neq`,
# identified by literal hash, are unfolded wherever they are applied to a
# type. Transcribed from `Syntax.tm_beta_eta_exeq_norm_1`.
_EX  = "912ad2cdc2d23bb8aa0a5070945f2a90976a948b0e8308917244591f3747f099"
_EQ  = "5a6af35fb6d6bea477dd0f822b8e01ca0d57cc50dfd41744307bc94597fdaa4a"
_NEQ = "7966a66a9bb198103c2a540ccd5ebebdff33c10843cc10eebfc98715e142989c"


def _eq_body(a):
    """All (a->a->prop). (DB0 DB2 DB1) -> (DB0 DB1 DB2)"""
    return ["ALL", ["AR", a, ["AR", a, ["PROP"]]],
            ["IMP", ["AP", ["AP", ["DB", "0"], ["DB", "2"]], ["DB", "1"]],
                    ["AP", ["AP", ["DB", "0"], ["DB", "1"]], ["DB", "2"]]]]


def _exeq_expand(e):
    """Unfold (TPAP (TMH <ex|eq|neq>) a), or None if not one of them."""
    if not (isinstance(e, list) and e[0] == "TPAP"
            and isinstance(e[1], list) and e[1][0] == "TMH"):
        return None
    h, a = e[1][1], e[2]
    if h == _EX:
        return ["LAM", ["AR", a, ["PROP"]],
                ["ALL", ["PROP"],
                 ["IMP", ["ALL", a, ["IMP", ["AP", ["DB", "2"], ["DB", "0"]],
                                            ["DB", "1"]]],
                         ["DB", "0"]]]]
    if h == _EQ:
        return ["LAM", a, ["LAM", a, _eq_body(a)]]
    if h == _NEQ:
        # the non-HF (Egal) branch, which is what these corpora use
        return ["LAM", a, ["LAM", a,
                           ["IMP", _eq_body(a), ["ALL", ["PROP"], ["DB", "0"]]]]]
    return None


def content_norm(e):
    """An *approximation* of Megalodon's `tm_beta_eta_exeq_norm`: contract
    beta-redexes (AP of LAM) and eta-redexes (LAM x. f x, where f does not
    use x), and unfold `ex` / `eq` / `neq` applied to a type. Innermost
    first, to a fixpoint.

    Deliberately called an approximation. Megalodon takes content hashes
    over this normal form, and the topology corpus has pairs
    (`omega_nonzero_neq_omega` / `Zplus_neq_omega`, and two
    `affine_line_R2_*` pairs) that Megalodon's own hasher assigns equal
    ids while this function still reports them as different. So there is
    at least one more equivalence in the real normaliser than is
    reproduced here, and chasing it would be reimplementing a kernel
    component in Python -- exactly the kind of fidelity risk this project
    exists to avoid. Equality is therefore decided downstream by
    Megalodon's own hashing code (`hashcheck.ml` + `compare_hashes.py`);
    this is used only to keep the audit's report quiet about differences
    that are known to be benign."""
    if not isinstance(e, list):
        return e
    exp = _exeq_expand(e)
    if exp is not None:
        return content_norm(exp)
    e = [e[0]] + [content_norm(c) for c in e[1:]]
    if e[0] == "AP" and isinstance(e[1], list) and e[1][0] == "LAM":
        return content_norm(_subst(e[1][2], 0, e[2]))
    if e[0] == "LAM" and isinstance(e[2], list) and e[2][0] == "AP" \
            and isinstance(e[2][2], list) and e[2][2] == ["DB", "0"] \
            and not _occurs(e[2][1], 0):
        return content_norm(_shift(e[2][1], -1))
    return e


# kept under the old name too: callers elsewhere mean the same thing
beta_eta_norm = content_norm


def norm_str(rendered):
    """Content normal form of an already-rendered s-expression."""
    return _render_sexpr(content_norm(parse_sexpr(rendered, 0)[0]))


# --------------------------------------------------- statement round-trip
def _render_sexpr(node):
    if isinstance(node, str):
        return node
    return "(" + " ".join(_render_sexpr(c) for c in node) + ")"


def audit_hash_consistency(forms):
    """Megalodon content-addresses every declaration, so a hash shared by
    two declarations is Megalodon itself asserting they denote the same
    object. That assertion is ground truth independent of this
    translator, so we check our view of those declarations against it.

    Two things need keeping straight, because a hash key means different
    things to different forms:

      * What the hash *denotes*. For DEF it is the defined term (the
        body), not the type; for AXIOM/THM it is the proposition. For
        PARAM/PRIM the object is opaque -- there is no body to compare.
      * What *type* the declaration gives it. DEF/PARAM/PRIM all state
        one; AXIOM/THM do not (their statement is the proposition).

    So denotations are compared against denotations and types against
    types, never across. Comparing a DEF's type field against a THM's
    proposition is how an earlier version of this check reported `True`
    and `TrueI` as a mismatch -- they are in fact perfectly consistent.

    One normalisation is needed. A declaration may denote the group's
    object by *naming* it: `TrueI`'s proposition is the bare
    `(TMH <key>)` where `<key>` is the group's own hash. That is a
    reference to the same object, not a competing claim about its
    structure, so it is consistent by construction and carries no
    structure to compare.

    This is *a* statement-level round-trip check, not a complete one: it
    catches inconsistent handling of declarations Megalodon itself says
    are identical, not e.g. a translator bug that is wrong the same way
    for every input (which Lean's kernel also can't catch, since a
    self-consistent mistranslation still type-checks against itself).
    Closing that gap needs the reverse direction -- Lean back to
    Megalodon, re-hashed by Megalodon's own code.
    """
    denotes = {}  # hash -> [(tag, name, denoted_sexpr)]
    types = {}    # hash -> [(tag, name, type_sexpr)]
    seen = set()

    for form in forms:
        tag = form[0]
        if tag == "DEF":
            # form: DEF name hash i ty tm -- hash denotes tm, not ty
            name, h, ty, tm = form[1], form[2], form[4], form[5]
            denotes.setdefault(h, []).append((tag, name, tm))
            types.setdefault(h, []).append((tag, name, ty))
        elif tag == "PARAM":
            # form: PARAM name hash i ty -- opaque object, type only
            name, h, ty = form[1], form[2], form[4]
            types.setdefault(h, []).append((tag, name, ty))
        elif tag == "PRIM":
            # form: PRIM idx name hash ty -- opaque object, type only
            name, h, ty = form[2], form[3], form[4]
            types.setdefault(h, []).append((tag, name, ty))
        elif tag == "AXIOM":
            # form: AXIOM name hash i prop -- hash denotes the proposition
            name, h, prop = form[1], form[2], form[4]
            denotes.setdefault(h, []).append((tag, name, prop))
        elif tag == "THM":
            # form: THM name ahv pfgahv i prop -- ahv denotes the proposition
            name, h, prop = form[1], form[2], form[5]
            denotes.setdefault(h, []).append((tag, name, prop))
        else:
            continue
        seen.add(h)

    def disagree(h, entries):
        """Entries claiming structure for hash h that do not agree.

        Two normalisations, both forced by how Megalodon assigns ids:

          * the id is taken over the beta-eta normal form, so entries are
            compared normalised -- `coarser_than` is `fun A B => Subq A B`
            and shares `Subq`'s hash;
          * an entry may denote the group's object by *naming* it, and
            after normalisation that is the bare `(TMH h)` (which is also
            what the eta-expanded form above reduces to). That is a
            reference, not a competing claim about structure, so it
            carries nothing to compare.
        """
        ref = "(TMH %s)" % h
        claims = []
        for t, n, node in entries:
            try:
                r = norm_str(_render_sexpr(node))
            except RecursionError:
                r = _render_sexpr(node)
            if r != ref:
                claims.append((t, n, r))
        if len(claims) < 2:
            return None
        if any(r != claims[0][2] for _, _, r in claims):
            return claims
        return None

    mismatches = []
    shared = 0
    for kind, table in (("denotation", denotes), ("type", types)):
        for h, entries in table.items():
            if len(entries) < 2:
                continue
            shared += 1
            bad = disagree(h, entries)
            if bad:
                mismatches.append((kind, h, bad))

    print("statement consistency report: %d declarations, %d hash groups "
          "with more than one claim, %d still differing after partial "
          "normalisation" % (len(seen), shared, len(mismatches)))
    for kind, h, claims in mismatches:
        print("  note (%s) %s...: %s  <- share a hash and differ "
              "structurally; benign if Megalodon's hasher agrees, which "
              "compare_hashes.py is what actually checks"
              % (kind, h[:16], [n for _, n, _ in claims]))
    return len(mismatches) == 0


# ---------------------------------------------------------------- driver
class Entry:
    __slots__ = ("name", "text", "deps", "category")
    def __init__(self, name, text, deps, category):
        self.name = name
        self.text = text          # full Lean declaration text
        self.deps = deps          # names this entry's text refers to
        self.category = category  # None for prelude items; a TIER_ORDER value for theorems


def translate(forms):
    ctx = Ctx()
    entries = []          # list[Entry], in source order
    thm_stmt = {}          # name -> (lean_type, ahv, tvs, deps_from_statement)
    ok, fail = 0, 0
    fail_examples = []

    def push_tpvars(i):
        """Empirically verified against func_ext (2 type params): the
        FIRST nested type-application at a call site binds the parameter
        declared LAST in the Lean signature -- push in reverse so TPVAR 0
        ends up as the first (outermost) declared Lean parameter."""
        names = [ctx.fresh("T") for _ in range(i)]
        ctx.tp_stack.extend(reversed(names))
        return names

    def pop_tpvars(names):
        if names:
            del ctx.tp_stack[-len(names):]

    def explicit_prefix(names):
        # EXPLICIT (plain parens), not implicit ({..}): Megalodon's own
        # term structure always instantiates a polymorphic type via an
        # explicit TpAp/PTpAp application node, never leaves it to
        # inference.
        return "".join(f"({n} : Type) " for n in names)

    for form in forms:
        tag = form[0]
        try:
            if tag == "PARAM":
                _, name, h, i, ty = form
                i = int(i)
                ctx.current_deps = set()
                tvs = push_tpvars(i)
                lty = tp_to_lean(ty, ctx)
                pop_tpvars(tvs)
                text = f"axiom {name} {explicit_prefix(tvs)}: {lty}"
                entries.append(Entry(name, text, ctx.current_deps, None))
                ctx.tm_hash_to_name[h] = name
            elif tag == "AXIOM":
                _, name, h, i, ty = form
                i = int(i)
                ctx.current_deps = set()
                tvs = push_tpvars(i)
                lty = tm_to_lean(ty, ctx)
                pop_tpvars(tvs)
                text = f"axiom {name} {explicit_prefix(tvs)}: {lty}"
                entries.append(Entry(name, text, ctx.current_deps, None))
                ctx.pf_hash_to_name[h] = name
            elif tag == "DEF":
                _, name, h, i, ty, tm = form
                i = int(i)
                ctx.current_deps = set()
                tvs = push_tpvars(i)
                lty = tp_to_lean(ty, ctx)
                ltm = tm_to_lean(tm, ctx)
                pop_tpvars(tvs)
                text = f"noncomputable def {name} {explicit_prefix(tvs)}: {lty} := {ltm}"
                entries.append(Entry(name, text, ctx.current_deps, None))
                ctx.tm_hash_to_name[h] = name
            elif tag == "PRIM":
                _, idx, name, h, ty = form
                ctx.current_deps = set()
                lty = tp_to_lean(ty, ctx)
                text = f"axiom {name} : {lty}"
                entries.append(Entry(name, text, ctx.current_deps, None))
                ctx.tm_hash_to_name[h] = name
                ctx.prim_to_name[int(idx)] = name
            elif tag == "THM":
                _, name, ahv, pfgahv, i, ty = form
                i = int(i)
                ctx.current_deps = set()
                tvs = push_tpvars(i)
                lty = tm_to_lean(ty, ctx)
                pop_tpvars(tvs)
                thm_stmt[name] = (lty, ahv, tvs, set(ctx.current_deps))
            elif tag == "PROOF":
                _, name, pf = form
                if name not in thm_stmt:
                    continue
                lty, ahv, tvs, stmt_deps = thm_stmt[name]
                ctx.current_deps = set(stmt_deps)
                ctx.tp_stack.extend(tvs)
                lpf = pf_to_lean(pf, ctx)
                pop_tpvars(tvs)
                text = f"theorem {name} {explicit_prefix(tvs)}: {lty} := {lpf}"
                category = categorise(name, lty, ctx.current_deps)
                entries.append(Entry(name, text, ctx.current_deps, category))
                ctx.pf_hash_to_name[ahv] = name
                ok += 1
        except Exception as e:
            fail += 1
            if len(fail_examples) < 15:
                fail_examples.append((tag, form[1] if len(form) > 1 else "?", str(e)[:120]))
            continue
        finally:
            ctx.current_deps = None

    print(f"translated OK: {ok}  failed: {fail}")
    for t, n, e in fail_examples:
        print(f"  FAIL {t} {n}: {e}")
    return entries


# `mgProp` is the identity on propositions. It exists so a binder type can
# be annotated without Lean beta-reducing it: an annotation is reduced
# during elaboration, but an *argument* is not, so `h : mgProp P` keeps `P`
# exactly as Megalodon wrote it. It is only emitted where a proposition
# contains a redex. Dropping the annotation instead would make Lean infer
# the binder type from the *statement*, which can differ from the
# proposition the proof recorded by eta as well as beta -- so annotating
# through this wrapper is the faithful choice, not just the convenient
# one. `reverse_translate.py` strips it. Being a plain reducible def, it
# is transparent to both the elaborator and the kernel.
HEADER = ("set_option maxRecDepth 8000\n\nnamespace Megalodon\n\n"
          "axiom set : Type\n\n"
          "@[reducible] def mgProp (p : Prop) : Prop := p\n\n")
FOOTER = "\nend Megalodon\n"


def render(entries):
    return HEADER + "\n".join(e.text for e in entries) + FOOTER


def render_category(all_entries, by_name, tier):
    """This tier's own theorems, plus the transitive closure of whatever
    prelude items and cross-category theorems they actually depend on,
    in original source order -- so the file is self-contained and
    (intended to be) independently compilable."""
    own = [e for e in all_entries if e.category == tier]
    need = set()
    frontier = list(own)
    while frontier:
        e = frontier.pop()
        for dep_name in e.deps:
            if dep_name in need:
                continue
            need.add(dep_name)
            if dep_name in by_name:
                frontier.append(by_name[dep_name])
    keep_names = need | {e.name for e in own}
    kept = [e for e in all_entries if e.name in keep_names]
    lines = [HEADER.rstrip("\n")]
    for e in kept:
        tag = "" if e.category is None else (
            "" if e.category == tier else f"  -- dependency from {e.category}")
        lines.append(e.text + tag)
    lines.append(FOOTER.strip("\n"))
    return "\n".join(lines) + "\n"


def main():
    text = open(sys.argv[1], encoding="utf-8").read()
    outdir = sys.argv[2]
    os.makedirs(outdir, exist_ok=True)
    forms = parse_toplevel_forms(text)

    # Reported, not enforced. Declarations that share a Megalodon hash are
    # guaranteed only to be equal under `tm_beta_eta_exeq_norm`, not to be
    # structurally identical, and `content_norm` above does not reproduce
    # that normal form exactly. Refusing to translate on a structural
    # difference therefore rejects valid corpora -- it blocked the topology
    # corpus on three pairs that Megalodon's own hasher says are equal. The
    # check that has teeth is `compare_hashes.py`, which re-derives every
    # id with Megalodon's code after the round trip.
    audit_hash_consistency(forms)

    entries = translate(forms)
    by_name = {e.name: e for e in entries}

    with open(os.path.join(outdir, "All.lean"), "w", encoding="utf-8") as f:
        f.write(render(entries))

    counts = {}
    for tier in TIER_ORDER:
        own = sum(1 for e in entries if e.category == tier)
        counts[tier] = own
        with open(os.path.join(outdir, f"{tier}.lean"), "w", encoding="utf-8") as f:
            f.write(render_category(entries, by_name, tier))

    total_thm = sum(counts.values())
    print("category counts (own theorems, not counting borrowed dependencies):")
    for tier in TIER_ORDER:
        print(f"  {tier:12s} {counts[tier]:4d}")
    print(f"  {'total':12s} {total_thm:4d}")


if __name__ == "__main__":
    main()
