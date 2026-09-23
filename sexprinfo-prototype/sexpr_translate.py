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
        self.hash_to_name = {}   # TMH/KNOWN hash -> Lean name
        self.prim_to_name = {}   # PRIM index -> Lean name
        self.tp_stack = []       # bound type-var names (TPVAR De Bruijn)
        self.tm_stack = []       # bound term-var names (DB De Bruijn)
        self.pf_stack = []       # bound proof-var names (Hyp De Bruijn)
        self.counter = 0
        self.current_deps = None  # set(), collected while translating one entry

    def fresh(self, base):
        self.counter += 1
        return f"{base}{self.counter}"

    def resolve_hash(self, h):
        name = self.hash_to_name[h]
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
        if h not in ctx.hash_to_name:
            raise KeyError(f"unresolved TMH hash (forward or missing reference): {h}")
        return ctx.resolve_hash(h)
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


def pf_to_lean(node, ctx):
    tag = node[0]
    if tag == "HYP":
        return ctx.pf_stack[-(int(node[1]) + 1)]
    if tag == "KNOWN":
        h = node[1]
        if h not in ctx.hash_to_name:
            raise KeyError(f"unresolved KNOWN hash: {h}")
        return ctx.resolve_hash(h)
    if tag == "PTMAP":
        return f"({pf_to_lean(node[1], ctx)} {tm_to_lean(node[2], ctx)})"
    if tag == "PPFAP":
        return f"({pf_to_lean(node[1], ctx)} {pf_to_lean(node[2], ctx)})"
    if tag == "PLAM":
        v = ctx.fresh("h")
        ty = tm_to_lean(node[1], ctx)
        ctx.pf_stack.append(v)
        body = pf_to_lean(node[2], ctx)
        ctx.pf_stack.pop()
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


# --------------------------------------------------- statement round-trip
def _render_sexpr(node):
    if isinstance(node, str):
        return node
    return "(" + " ".join(_render_sexpr(c) for c in node) + ")"


def audit_hash_consistency(forms):
    """Megalodon content-addresses every declaration: two declarations
    that Megalodon considers definitionally the same statement get the
    same hash (we found 8 such pairs in the reference corpus, e.g.
    `pair_Sigma` and `lamI`). That hash is ground truth independent of
    this translator. This check uses it as one: for every hash claimed
    by more than one PARAM/AXIOM/DEF/PRIM/THM, verify the raw statement
    s-expressions are structurally identical.

    Since translation is a deterministic, purely structural function of
    that s-expression (no surface text, no ambiguity to resolve), byte-
    identical raw structure guarantees shape-identical Lean output --
    so this transitively confirms the translator treats every such pair
    consistently, without needing to separately diff the rendered Lean
    text (which would differ cosmetically in fresh variable numbering
    even when the shape is identical).

    This is *a* statement-level round-trip check, not a complete one: it
    catches inconsistent handling of declarations Megalodon itself says
    are identical, not e.g. a translator bug that is wrong the same way
    for every input (which Lean's kernel also can't catch, since a
    self-consistent mistranslation still type-checks against itself).
    """
    claims = {}  # hash -> [(tag, name, raw_ty_sexpr_node), ...]
    for form in forms:
        tag = form[0]
        if tag in ("PARAM", "AXIOM"):
            name, h, i, ty = form[1], form[2], form[3], form[4]
            claims.setdefault(h, []).append((tag, name, ty))
        elif tag == "DEF":
            name, h, i, ty, tm = form[1], form[2], form[3], form[4], form[5]
            claims.setdefault(h, []).append((tag, name, ty))
        elif tag == "PRIM":
            idx, name, h, ty = form[1], form[2], form[3], form[4]
            claims.setdefault(h, []).append((tag, name, ty))
        elif tag == "THM":
            name, ahv, pfgahv, i, ty = form[1], form[2], form[3], form[4], form[5]
            claims.setdefault(ahv, []).append((tag, name, ty))

    collisions = {h: v for h, v in claims.items() if len(v) > 1}
    mismatches = []
    for h, entries in collisions.items():
        raws = [_render_sexpr(ty) for _, _, ty in entries]
        if any(r != raws[0] for r in raws):
            mismatches.append((h, entries))

    print(f"statement round-trip audit: {len(claims)} declarations, "
          f"{len(collisions)} share a hash with at least one other, "
          f"{len(mismatches)} of those disagree on raw structure")
    for h, entries in mismatches:
        names = [n for _, n, _ in entries]
        print(f"  MISMATCH {h[:16]}...: {names}  <- these share a hash but "
              f"have different statement structure, investigate")
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
                ctx.hash_to_name[h] = name
            elif tag == "AXIOM":
                _, name, h, i, ty = form
                i = int(i)
                ctx.current_deps = set()
                tvs = push_tpvars(i)
                lty = tm_to_lean(ty, ctx)
                pop_tpvars(tvs)
                text = f"axiom {name} {explicit_prefix(tvs)}: {lty}"
                entries.append(Entry(name, text, ctx.current_deps, None))
                ctx.hash_to_name[h] = name
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
                ctx.hash_to_name[h] = name
            elif tag == "PRIM":
                _, idx, name, h, ty = form
                ctx.current_deps = set()
                lty = tp_to_lean(ty, ctx)
                text = f"axiom {name} : {lty}"
                entries.append(Entry(name, text, ctx.current_deps, None))
                ctx.hash_to_name[h] = name
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
                ctx.hash_to_name[ahv] = name
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


HEADER = "set_option maxRecDepth 8000\n\nnamespace Megalodon\n\naxiom set : Type\n\n"
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

    consistent = audit_hash_consistency(forms)
    if not consistent:
        print("REFUSING TO TRANSLATE: statement round-trip audit found a "
              "real mismatch (see above). Fix it before trusting the "
              "output.")
        sys.exit(1)

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
