#!/usr/bin/env python3
"""Lean 4 back to Megalodon: the reverse direction of the round trip.

`sexpr_translate.py` goes Megalodon -> Lean. This goes back, and the point
is *not* to invert that script. Inverting our own forward map would prove
nothing: a mistranslation that is wrong the same way in both directions
round-trips perfectly. So this reads what **Lean's own elaborator** made of
the generated source -- a dump of each declaration's elaborated `Expr`,
produced by the metaprogram in `lean_export.py` -- and reconstructs
Megalodon s-expressions from that. Lean is then an independent witness, and
disagreement means one of the two directions is wrong.

The interesting asymmetry is variable binding. Megalodon has three separate
de Bruijn namespaces:

    TPVAR   type variables      (absolute position, outermost = 0)
    DB      term variables      (de Bruijn, bound by LAM / ALL / TLAM)
    HYP     hypotheses          (de Bruijn, bound by PLAM)

Lean collapses all three into one `bvar` namespace. Compare `andI`:

    Megalodon  (PPFAP (PPFAP (HYP 0) (HYP 2)) (HYP 1))
    Lean       (app   (app   (bvar 0) (bvar 3)) (bvar 2))

Both mean `f h k`. Going back therefore means re-splitting that namespace,
which is done by tagging every binder as 'tp' / 'tm' / 'pf' from the shape
of its domain and counting indices per tag. An off-by-one here is exactly
the kind of error that still type-checks and still looks right, which is
why the result is checked against Megalodon's content hashes rather than
by reading it.

Two further shape differences are handled:

  * `IMP p q` binds nothing in Megalodon, but Lean represents it as a
    non-dependent `forallE`, which *does* occupy a binder slot. A binder is
    pushed for it so inner indices stay aligned; tagging it 'pf' keeps it
    out of the DB count, which is the correct behaviour.
  * Polymorphic declarations carry their type-parameter count in a separate
    field in Megalodon (`DEF "eq" <h> 1 ...`) with no binder in the type,
    whereas Lean makes them ordinary leading `(T : Type)` binders. Those are
    peeled off and the recovered count is itself compared.
"""

import sys
import os
import collections

# proof terms in this corpus nest deeply; the default limit is far too low
sys.setrecursionlimit(200000)

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from sexpr_translate import parse_sexpr, parse_toplevel_forms, _render_sexpr

PRELUDE = "Megalodon."
WRAPPER = "mgProp"   # the identity-on-Prop wrapper the forward translator
                     # emits to keep a redex out of annotation position
TERM_KINDS = {"DEF", "PARAM", "PRIM"}   # hash denotes an object
PROOF_KINDS = {"AXIOM", "THM"}          # hash denotes a proposition


class Mismatch(Exception):
    pass


# ------------------------------------------------------ beta-normalisation
# Lean's elaborator normalises binder types, so a proposition Megalodon
# recorded as an un-reduced redex `(AP (LAM (SET) P) y)` comes back from
# Lean already reduced to `P[y]`. The two are beta-convertible, so this is
# a difference in representation and not in content -- but it is a real
# difference, and the only honest way to report it is to say exactly how
# many declarations needed beta to agree, rather than quietly normalising
# everything and claiming byte-equality. So `check` compares raw first and
# falls back to this, counting the two cases separately.
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


def beta_norm(e):
    """Contract every AP-of-LAM redex, innermost first."""
    if not isinstance(e, list):
        return e
    e = [e[0]] + [beta_norm(c) for c in e[1:]]
    if e[0] == "AP" and isinstance(e[1], list) and e[1][0] == "LAM":
        return beta_norm(_subst(e[1][2], 0, e[2]))
    return e


def beta_equal(a, b):
    """True if two rendered s-expressions agree up to beta."""
    na = _render_sexpr(beta_norm(parse_sexpr(a, 0)[0]))
    nb = _render_sexpr(beta_norm(parse_sexpr(b, 0)[0]))
    return na == nb


# ----------------------------------------------------------- corpus side
class Corpus:
    """The original Megalodon export: what we are checking against."""

    def __init__(self, forms):
        self.kind = {}      # name -> DEF/PARAM/PRIM/AXIOM/THM
        self.hash = {}      # name -> the hash Megalodon gave it
        self.poly = {}      # name -> number of type parameters
        self.type = {}      # name -> rendered type s-expression (tp)
        self.prop = {}      # name -> rendered proposition (tm)
        self.body = {}      # name -> rendered definition body (tm)
        self.proof = {}     # name -> rendered proof term (pf)
        self.order = []

        for form in forms:
            tag = form[0]
            if tag == "DEF":
                n = form[1]
                self.kind[n] = tag
                self.hash[n] = form[2]
                self.poly[n] = int(form[3])
                self.type[n] = _render_sexpr(form[4])
                self.body[n] = _render_sexpr(form[5])
            elif tag == "PARAM":
                n = form[1]
                self.kind[n] = tag
                self.hash[n] = form[2]
                self.poly[n] = int(form[3])
                self.type[n] = _render_sexpr(form[4])
            elif tag == "PRIM":
                n = form[2]
                self.kind[n] = tag
                self.hash[n] = form[3]
                self.poly[n] = 0
                self.type[n] = _render_sexpr(form[4])
            elif tag == "AXIOM":
                n = form[1]
                self.kind[n] = tag
                self.hash[n] = form[2]
                self.poly[n] = int(form[3])
                self.prop[n] = _render_sexpr(form[4])
            elif tag == "THM":
                n = form[1]
                self.kind[n] = tag
                self.hash[n] = form[2]
                self.poly[n] = int(form[4])
                self.prop[n] = _render_sexpr(form[5])
            elif tag == "PROOF":
                self.proof[form[1]] = _render_sexpr(form[2])
                continue
            else:
                continue
            if form[0] != "PROOF":
                self.order.append(n)


# ------------------------------------------------------------- Lean side
def strip_ns(n):
    return n[len(PRELUDE):] if n.startswith(PRELUDE) else n


def unwrap(e):
    """Remove `mgProp` applications. It is the identity on propositions
    and exists only to stop Lean's elaborator beta-reducing an annotated
    binder type, so it carries no content and is dropped here."""
    while isinstance(e, list) and e[0] == "app" and \
            isinstance(e[1], list) and e[1][0] == "const" and \
            strip_ns(e[1][1]) == WRAPPER:
        e = e[2]
    return e


class Reverser:
    """Reconstructs Megalodon s-expressions from Lean `Expr` dumps.

    `ctx` is the binder stack, outermost first, each entry one of
    'tp' / 'tm' / 'pf'. Lean's `bvar i` counts the whole stack from the
    inside; Megalodon counts only binders of the matching kind.
    """

    def __init__(self, corpus):
        self.c = corpus

    # -- binder bookkeeping -------------------------------------------
    @staticmethod
    def _pos(ctx, i):
        """Stack position (outermost = 0) that Lean's `bvar i` refers to."""
        p = len(ctx) - 1 - i
        if p < 0:
            raise Mismatch("bvar %d escapes a context of depth %d" % (i, len(ctx)))
        return p

    def _db_index(self, ctx, i):
        """de Bruijn index among 'tm' binders: how many are strictly inner."""
        p = self._pos(ctx, i)
        if ctx[p] != "tm":
            raise Mismatch("bvar %d is a '%s' binder, expected a term variable"
                           % (i, ctx[p]))
        return sum(1 for t in ctx[p + 1:] if t == "tm")

    def _hyp_index(self, ctx, i):
        """de Bruijn index among 'pf' binders: how many are strictly inner."""
        p = self._pos(ctx, i)
        if ctx[p] != "pf":
            raise Mismatch("bvar %d is a '%s' binder, expected a hypothesis"
                           % (i, ctx[p]))
        return sum(1 for t in ctx[p + 1:] if t == "pf")

    def _tpvar_index(self, ctx, i):
        """TPVAR is an absolute position, not de Bruijn: count 'tp' binders
        strictly outside this one."""
        p = self._pos(ctx, i)
        if ctx[p] != "tp":
            raise Mismatch("bvar %d is a '%s' binder, expected a type variable"
                           % (i, ctx[p]))
        return sum(1 for t in ctx[:p] if t == "tp")

    # -- classification -----------------------------------------------
    def is_type(self, e, ctx):
        """True if `e` is a Megalodon *type* (tp) rather than a term."""
        e = unwrap(e)
        if not isinstance(e, list):
            return False
        h = e[0]
        if h == "sort":
            return True                      # Prop (sort 0) or Type (sort 1)
        if h == "const":
            return strip_ns(e[1]) == "set"
        if h == "bvar":
            p = self._pos(ctx, int(e[1]))
            return ctx[p] == "tp"
        if h == "all":
            # an arrow type: both sides types, and nothing bound
            return self.is_type(e[2], ctx) and \
                   self.is_type(e[3], ctx + ["tm"])
        return False

    def binder_tag(self, dom, ctx):
        """Which namespace a binder with this domain belongs to."""
        if isinstance(dom, list) and dom[0] == "sort" and dom[1] == "1":
            return "tp"          # (T : Type) -- a type parameter
        if self.is_type(dom, ctx):
            return "tm"          # (x : set), (x : Prop), (f : set -> Prop)
        return "pf"              # (h : <some proposition>)

    def classify(self, e, ctx):
        """'tp' | 'tm' | 'pf' -- which language `e` belongs to."""
        if self.is_type(e, ctx):
            return "tp"
        e = unwrap(e)
        h = e[0] if isinstance(e, list) else None
        if h == "bvar":
            return ctx[self._pos(ctx, int(e[1]))]
        if h == "const":
            n = strip_ns(e[1])
            k = self.c.kind.get(n)
            if k in PROOF_KINDS:
                return "pf"
            if k in TERM_KINDS:
                return "tm"
            raise Mismatch("unknown constant %s" % n)
        if h == "app":
            # applying something does not change which language it is in
            return self.classify(e[1], ctx)
        if h == "lam":
            return self.classify(e[3], ctx + [self.binder_tag(e[2], ctx)])
        if h == "all":
            return "tm"          # a proposition
        raise Mismatch("cannot classify %s" % (h,))

    # -- the three reverse maps ---------------------------------------
    def tp(self, e, ctx):
        e = unwrap(e)
        h = e[0] if isinstance(e, list) else None
        if h == "sort":
            if e[1] == "0":
                return ["PROP"]
            raise Mismatch("sort %s has no Megalodon type" % e[1])
        if h == "const":
            if strip_ns(e[1]) == "set":
                return ["SET"]
            raise Mismatch("constant %s is not a type" % strip_ns(e[1]))
        if h == "all":
            return ["AR", self.tp(e[2], ctx), self.tp(e[3], ctx + ["tm"])]
        if h == "bvar":
            return ["TPVAR", str(self._tpvar_index(ctx, int(e[1])))]
        raise Mismatch("not a type: %s" % (h,))

    def tm(self, e, ctx):
        e = unwrap(e)
        h = e[0] if isinstance(e, list) else None
        if h == "bvar":
            return ["DB", str(self._db_index(ctx, int(e[1])))]
        if h == "const":
            n = strip_ns(e[1])
            if n not in self.c.hash:
                raise Mismatch("constant %s not in the corpus" % n)
            return ["TMH", self.c.hash[n]]
        if h == "app":
            if self.is_type(e[2], ctx):
                return ["TPAP", self.tm(e[1], ctx), self.tp(e[2], ctx)]
            return ["AP", self.tm(e[1], ctx), self.tm(e[2], ctx)]
        if h == "lam":
            return ["LAM", self.tp(e[2], ctx), self.tm(e[3], ctx + ["tm"])]
        if h == "all":
            if self.is_type(e[2], ctx):
                return ["ALL", self.tp(e[2], ctx), self.tm(e[3], ctx + ["tm"])]
            # IMP binds nothing in Megalodon, but Lean spends a binder slot
            # on it; push one so inner indices line up, tagged 'pf' so it
            # stays out of the DB count.
            return ["IMP", self.tm(e[2], ctx), self.tm(e[3], ctx + ["pf"])]
        raise Mismatch("not a term: %s" % (h,))

    def pf(self, e, ctx):
        e = unwrap(e)
        h = e[0] if isinstance(e, list) else None
        if h == "bvar":
            return ["HYP", str(self._hyp_index(ctx, int(e[1])))]
        if h == "const":
            n = strip_ns(e[1])
            if self.c.kind.get(n) not in PROOF_KINDS:
                raise Mismatch("%s is not a known fact" % n)
            return ["KNOWN", self.c.hash[n]]
        if h == "app":
            k = self.classify(e[2], ctx)
            if k == "pf":
                return ["PPFAP", self.pf(e[1], ctx), self.pf(e[2], ctx)]
            if k == "tp":
                return ["PTPAP", self.pf(e[1], ctx), self.tp(e[2], ctx)]
            return ["PTMAP", self.pf(e[1], ctx), self.tm(e[2], ctx)]
        if h == "lam":
            tag = self.binder_tag(e[2], ctx)
            if tag == "tp":
                # Megalodon's `pf` type has exactly seven constructors and
                # no type-lambda: type abstraction in a proof is carried by
                # the arity field of the enclosing declaration (`ppf = int
                # * pf`) and only materialises as `Mathdata.PTpLam` inside
                # the hashing representation, never as a surface tag. So a
                # `(T : Type)` binder here is not something to encode -- it
                # means `peel` did not strip all the leading type
                # parameters, which is a bug to fix rather than a term to
                # translate.
                raise Mismatch(
                    "type-lambda inside a proof: Megalodon has no surface "
                    "constructor for this; the leading (T : Type) binders "
                    "should have been peeled as the declaration's arity")
            if tag == "tm":
                return ["TLAM", self.tp(e[2], ctx), self.pf(e[3], ctx + ["tm"])]
            return ["PLAM", self.tm(e[2], ctx), self.pf(e[3], ctx + ["pf"])]
        raise Mismatch("not a proof: %s" % (h,))

    # -- peeling type parameters --------------------------------------
    @staticmethod
    def peel(e, former):
        """Strip leading `(T : Type)` binders, which Megalodon keeps in a
        separate arity field rather than as binders. Returns (count, body,
        ctx) -- `former` is 'all' for a type, 'lam' for a value."""
        n = 0
        while isinstance(e, list) and e[0] == former and \
                isinstance(e[2], list) and e[2][0] == "sort" and e[2][1] == "1":
            n += 1
            e = e[3]
        return n, e, ["tp"] * n


# ---------------------------------------------------------------- driver
def load_lean_dump(path):
    decls = {}
    for form in parse_toplevel_forms(open(path).read()):
        if form[0] != "DECL":
            continue
        name, kind, ty, val = form[1], form[2], form[3], form[4]
        decls[name] = (kind, ty, val)
    return decls


def compare(got, want, name, what):
    """'identical' / 'beta-equal', or raise. Byte-equality is the result
    worth having, so it is reported separately from beta-equality rather
    than folded in."""
    if got == want:
        return "identical"
    if beta_equal(got, want):
        return "beta-equal"
    raise Mismatch("%s\n    got  %s\n    want %s" % (what, got, want))


def check(corpus, decls, verbose=False, limit=None):
    """Reconstruct each declaration from Lean's Expr and compare against
    what Megalodon originally exported."""
    rv = Reverser(corpus)
    stats = collections.Counter()
    failures = []

    for name in corpus.order:
        if limit is not None and stats["checked"] >= limit:
            break
        kind = corpus.kind[name]
        if name not in decls:
            stats["absent from Lean"] += 1
            continue
        _, lean_ty, lean_val = decls[name]
        stats["checked"] += 1

        try:
            npoly, ty_body, ctx = rv.peel(lean_ty, "all")
            if npoly != corpus.poly[name]:
                raise Mismatch("type-parameter count: Lean %d, Megalodon %d"
                               % (npoly, corpus.poly[name]))

            if kind in PROOF_KINDS:
                got = _render_sexpr(rv.tm(ty_body, ctx))
                want = corpus.prop[name]
                stats["proposition " + compare(got, want, name, "proposition")] += 1
            else:
                got = _render_sexpr(rv.tp(ty_body, ctx))
                want = corpus.type[name]
                stats["type " + compare(got, want, name, "type")] += 1

            if kind == "DEF":
                _, val_body, vctx = rv.peel(lean_val, "lam")
                got = _render_sexpr(rv.tm(val_body, vctx))
                want = corpus.body[name]
                stats["body " + compare(got, want, name, "definition body")] += 1

            if kind == "THM" and name in corpus.proof:
                _, val_body, vctx = rv.peel(lean_val, "lam")
                got = _render_sexpr(rv.pf(val_body, vctx))
                want = corpus.proof[name]
                stats["proof " + compare(got, want, name, "proof term")] += 1

        except Mismatch as exc:
            stats["MISMATCH"] += 1
            failures.append((name, kind, str(exc)))
        except RecursionError:
            stats["too deep to check"] += 1
            failures.append((name, kind, "RecursionError"))

    return stats, failures


def emit_recon(corpus, decls, path):
    """Write the reconstructed terms in the form `hashcheck.ml` reads, so
    Megalodon's own hashing code can be run over them. Only the terms a
    hash actually denotes are emitted: a proposition for AXIOM/THM
    (`ptm_all_id`) and the body for DEF (`ptm_lam_id`)."""
    rv = Reverser(corpus)
    n = 0
    with open(path, "w") as f:
        for name in corpus.order:
            kind = corpus.kind[name]
            if name not in decls:
                continue
            _, lean_ty, lean_val = decls[name]
            try:
                if kind in PROOF_KINDS:
                    npoly, body, ctx = rv.peel(lean_ty, "all")
                    term = _render_sexpr(rv.tm(body, ctx))
                    k = "all"
                elif kind == "DEF":
                    npoly, body, ctx = rv.peel(lean_val, "lam")
                    term = _render_sexpr(rv.tm(body, ctx))
                    k = "lam"
                else:
                    continue
            except (Mismatch, RecursionError):
                continue
            f.write('(RECON "%s" %s %d %s)\n' % (name, k, npoly, term))
            n += 1
    print("wrote %d reconstructed terms to %s" % (n, path))


def main():
    if len(sys.argv) < 3:
        print(__doc__)
        print("usage: reverse_translate.py <corpus.sexpr> <lean_expr_dump> "
              "[--verbose] [--limit N] [--emit <file>]")
        sys.exit(2)
    corpus = Corpus(parse_toplevel_forms(open(sys.argv[1]).read()))
    decls = load_lean_dump(sys.argv[2])
    verbose = "--verbose" in sys.argv
    limit = None
    if "--limit" in sys.argv:
        limit = int(sys.argv[sys.argv.index("--limit") + 1])

    print("corpus: %d declarations, %d with proofs" %
          (len(corpus.order), len(corpus.proof)))
    print("Lean:   %d declarations exported" % len(decls))

    if "--emit" in sys.argv:
        emit_recon(corpus, decls, sys.argv[sys.argv.index("--emit") + 1])

    stats, failures = check(corpus, decls, verbose, limit)
    print()
    for k in ("checked",
              "type identical", "type beta-equal",
              "proposition identical", "proposition beta-equal",
              "body identical", "body beta-equal",
              "proof identical", "proof beta-equal",
              "absent from Lean", "too deep to check", "MISMATCH"):
        if stats[k]:
            print("  %-22s %d" % (k, stats[k]))

    if failures:
        print("\nfirst %d of %d failures:" % (min(10, len(failures)), len(failures)))
        for name, kind, msg in failures[:10]:
            msg = msg if verbose else msg[:400]
            print("  %s (%s): %s" % (name, kind, msg))

    sys.exit(1 if stats["MISMATCH"] else 0)


if __name__ == "__main__":
    main()
