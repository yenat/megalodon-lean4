# sexprinfo prototype: a complete, working proof-term translator

This started as reconnaissance for translating from Megalodon's own
structured, typed, de-Bruijn, content-addressed export instead of
hand-parsed `.mg` surface text (see the main README's "Where this goes
next"). It is no longer just reconnaissance: `sexpr_translate.py` is a
working translator, built and verified end to end on the same 999-theorem
reference corpus (`100thms_12.mg`) the main translator uses.

## Result

**999 / 999 theorems verified — 100% — with zero `sorry` and zero
`sorryAx`.** Confirmed by both a full recompile of `verified_output/All.lean`
and an independent `#print axioms` pass over every theorem. The only
axioms used are Megalodon's own 17 foundational ones (`Empty`, `In_ind`,
`set_ext`, `func_ext`, `prop_ext`, `Eps_i`, `Eps_i_ax`, `UnivOf`, and
similar) — the same axiom set the tactic-based translator's output
depends on, nothing extra assumed.

This includes every theorem in the surreal-number category, which was the
tactic-based translator's persistent weak point (23-24% all day) — here
it's 593/593.

**The mgwiki library now verifies too: the whole `Part1.mg`–`Part14.mg`
chain (1401 / 1401 theorems) and
`topology_begin_wout_woax_wpreamble.mg` (933 / 933), both with zero Lean
errors and zero `sorry`.** 26 of the 31 files in `mglib/` export; see
"Known rough edges" for how, and for the 5 that need a Megalodon build
newer than any published source.

All three corpora — 3333 theorems — also survive the reverse direction
with every content hash reproduced. See "The reverse direction" below,
which is the stronger claim and the one worth reading first.

Also prints a statement-level consistency report
(`audit_hash_consistency`): Megalodon content-addresses every declaration,
so a hash shared by two declarations is Megalodon itself asserting they
denote the same object, and it is worth looking at how we treat each such
group rather than trusting that "Lean accepted it" means "it's the right
statement." The reference corpus has 8 such groups (e.g. `pair_Sigma` and
`lamI`).

It is a report and not a gate, which it had to become. Two things make a
structural comparison the wrong thing to enforce:

- **A hash key means different things to different forms.** For a `DEF` it
  denotes the defined *term* (the body, not the type); for `AXIOM`/`THM`
  the *proposition*; for `PARAM`/`PRIM` the object is opaque and only its
  type is stated. Pooling those is how an earlier version reported `True`
  and `TrueI` as a mismatch when they are perfectly consistent.
  Denotations are now compared against denotations and types against
  types, never across.
- **Sharing a hash does not imply structural identity.** Megalodon hashes
  the `tm_beta_eta_exeq_norm` normal form, so `coarser_than`, defined as
  `fun A B => Subq A B`, shares `Subq`'s hash while being its
  eta-expansion. Normalising is therefore mandatory, and `content_norm`
  only *approximates* Megalodon's normaliser: the topology corpus has
  three pairs it still separates which Megalodon's own hasher assigns
  equal ids. Closing that gap would mean reimplementing a kernel component
  in Python, which is the fidelity risk this project exists to avoid.

So structural equality is reported for information, and the check with
teeth is `compare_hashes.py`, which re-derives every id with Megalodon's
own code after the round trip. Enforcing the structural version rejected a
valid corpus; enforcing the hash version does not.

The namespace bug above was latent on the reference corpus and surfaced
immediately on `Part1.mg`; the normalisation bug surfaced only on the
topology corpus. That is the argument for running on more than one corpus,
in two sentences.

## The reverse direction: Lean back to Megalodon, checked by hash

`reverse_translate.py` closes the loop, and `hashcheck.ml` closes it on
Megalodon's terms rather than ours.

The point is **not** to invert the forward map. That would prove nothing: a
mistranslation that is wrong the same way in both directions round-trips
perfectly and reproduces the hash. So the reverse direction reads what
**Lean's own elaborator** made of the generated source -- `lean_export.lean`
is a metaprogram that dumps each declaration's elaborated `Expr` -- and
reconstructs Megalodon s-expressions from that. Lean is then an independent
witness rather than a mirror.

The final step hands those reconstructed terms back to Megalodon's own
hashing code (`Syntax.ptm_all_id` / `ptm_lam_id` -- the functions Megalodon
uses to assign a declaration its id) and compares the result against the ids
in the original export. Nothing is reimplemented: the hashes are computed by
Megalodon.

### Results

| corpus | theorems | Lean errors | statements identical | proofs identical | hashes matching |
|---|---|---|---|---|---|
| `mglib/Part1.mg` … `Part14.mg` | 1401 | 0 | **1600 / 1600** | **1401 / 1401** | **1593 / 1593** |
| `100thms_12.mg` | 999 | 0 | **1158 / 1158** | **999 / 999** | **1151 / 1151** |
| `topology_begin_wout_woax_wpreamble.mg` | 933 | 0 | **2347 / 2347** | **933 / 933** | **2340 / 2340** |
| **total** | **3333** | **0** | **5105 / 5105** | **3333 / 3333** | **5084 / 5084** |

Byte-identical at the raw s-expression level, not up to a normalisation, and
every recomputed content hash equal to the one Megalodon originally assigned.
Zero disagreements.

The axiom audit holds across the new corpora too: `#print axioms` over all
1401 theorems of the `Part1`–`Part14` chain reports zero `sorryAx`, zero
`Classical.choice`, and nothing outside Megalodon's own foundational
axioms (26 theorems depend on no axioms at all). The `mgProp` wrapper the
forward translator emits is a plain reducible `def`, so it adds nothing to
that set.

`hash_negative_control.py` checks that this is not vacuous. It perturbs each
reconstructed term in a way that keeps it well-formed but changes its
meaning -- swapping the operands of one application -- and confirms Megalodon
assigns a different id. Across the three corpora, **5030 / 5030**
perturbations change the hash; none survives.

### Why this catches things nothing else does

Megalodon has three separate de Bruijn namespaces -- `TPVAR` for type
variables, `DB` for term variables, `HYP` for hypotheses -- and Lean
collapses all three into one `bvar`. Compare `andI`:

```
Megalodon  (PPFAP (PPFAP (HYP 0) (HYP 2)) (HYP 1))
Lean       (app   (app   (bvar 0) (bvar 3)) (bvar 2))
```

Both mean `f h k`. Going back means re-splitting that namespace by tagging
every binder from the shape of its domain. An off-by-one there still
type-checks and still reads correctly. The same goes for `IMP` versus `ALL`,
which are both `forallE` in Lean.

Three real bugs came out of building this, none of which Lean's kernel could
have caught -- a self-consistent mistranslation type-checks against itself:

- **The audit pooled hash namespaces.** It reported `True` and `TrueI` as a
  mismatch when they are consistent. A `DEF`'s hash denotes its *body*, an
  `AXIOM`/`THM`'s denotes its *proposition*, and a `PARAM`/`PRIM`'s object is
  opaque. Fixed by comparing denotations against denotations and types
  against types.
- **The forward translator kept one hash → name map.** `True` (a `DEF`) and
  `TrueI` (a `THM`) share a hash, so `TMH` in a term and `KNOWN` in a proof
  resolved to whichever was declared last. Latent on the reference corpus,
  92 Lean errors on the `Part1`–`Part14` chain. Fixed with separate maps.
- **Lean beta-reduces a `fun`'s type annotation.** Megalodon records
  un-reduced redexes in `PLAM` propositions, so 152 proof terms came back
  reduced. Fixed with an `@[reducible] def mgProp (p : Prop) : Prop := p`
  wrapper that keeps the proposition in argument rather than annotation
  position. Dropping the annotation instead is *wrong*: Lean then infers the
  binder type from the statement, which can differ from the proof's recorded
  proposition by eta as well -- `SchroederBernstein` is the case that shows
  it.

### What this does and does not establish

It establishes that the translation is faithful: nothing is lost or garbled
in either direction, checked against Megalodon's own content hashes rather
than by eye or by "Lean accepted it."

It does **not** establish that the Lean axiomatisation is a sound model of
Megalodon's higher-order Tarski-Grothendieck set theory. A round trip cannot
tell you the axioms are right; that is what the axiom audit argues,
separately. The two claims are easy to conflate.

Two facts about Megalodon's hashing are worth recording, because they bound
what the hash check can mean. `Syntax.tm_id` hashes a term *after*
`tm_beta_eta_exeq_norm`, so content hashes are already beta-eta normalised --
the byte-identical proof terms above are a stronger result than matching
hashes alone would require. And `Syntax.ppf_id` is stubbed to return zeros,
so Megalodon content-addresses propositions, not proof terms: there is no
proof hash to reproduce, which is why the proof terms are compared
structurally and the hashes are compared for statements and definition
bodies.

### Reproducing

```bash
# forward
python3 sexpr_translate.py corpus.sexpr out/
lean -D maxErrors=50000 out/All.lean          # expect no output

# Lean's elaborated terms back out
printf 'import Lean\nset_option linter.unusedVariables false\n' > export.lean
cat out/All.lean lean_export.lean >> export.lean
MEGALODON_EXPR_OUT=corpus_expr.sexpr lean export.lean

# reverse, then hash with Megalodon's own code
python3 reverse_translate.py corpus.sexpr corpus_expr.sexpr --emit recon.txt
<megalodon>/bin/hashcheck recon.txt > recon_hashes.txt
python3 compare_hashes.py corpus.sexpr recon_hashes.txt
python3 hash_negative_control.py recon.txt <megalodon>/bin/hashcheck
```

`hashcheck.ml` builds against a built Megalodon tree:

```bash
cp hashcheck.ml <megalodon>/ && cd <megalodon>
ocamlopt -I bin -o bin/hashcheck unix.cmxa bin/ser.cmx bin/hashaux.cmx \
  bin/sha256.cmx bin/hash.cmx bin/mathdata.cmx bin/mathdatapfg.cmx \
  bin/syntax.cmx hashcheck.ml
```

## Why this works where the surface-text translator struggles

The tactic-based translator (`megalodon_full.py`) hand-parses Megalodon's
`.mg` source text with regexes and bracket-counting scanners, then maps
Megalodon's own tactic scripts onto Lean tactics line by line. Every bug
fixed in that translator today (parenthesization, tuple-comma ambiguity,
a regex character class missing an apostrophe, precedence) traced back to
the same root: text is genuinely ambiguous, and hand-written parsing of
it is genuinely fragile, especially across the very long, deeply nested
proofs that make up most of the surreal-number category.

This translator instead consumes Megalodon's own already-elaborated,
already-typed proof *term* — a small, closed set of constructors
(`DB`/`TmH`/`Prim`/`TpAp`/`Ap`/`Lam`/`Imp`/`All` for terms;
`Hyp`/`Known`/`PTpAp`/`PTmAp`/`PPfAp`/`PLam`/`TLam` for proofs, which is
all seven of them), each theorem's proof referencing earlier facts by
content hash rather than by name. `APPENDIX.md` documents every tag. There is
no surface syntax left to mis-parse, so this entire class of bug cannot
recur here by construction, not by further patching.

## What's here

- `pf_to_sexpr.patch` / `megalodon.ml.patched` — the one-line patch
  against upstream Megalodon (`https://github.com/ai4reason/Megalodon`)
  that wires the already-existing `pf_to_sexpr` function into
  `-sexprinfo`'s output, so it emits each theorem's checked proof term
  (`PROOF "<name>" <sexpr>`) alongside its statement (`THM ...`).
- `sexpr_translate.py` — the translator: an S-expression parser, a
  `tp`/`tm`/`pf` -> Lean 4 term compiler (~230 lines), and a driver that
  reads a `-sexprinfo` dump and writes a single Lean file.
- `verified_output/` — the full, verified output: `All.lean` (all 999
  theorems, one file, authoritative) plus `prop_logic.lean` /
  `set_theory.lean` / `nat_arith.lean` / `ordinals.lean` /
  `surreals.lean`, each including only the prelude items and
  cross-category theorems it actually depends on. All six files
  compile standalone with zero errors -- unlike the tactic-based
  translator's category split, which has a known cross-dependency gap
  (see the main README's Limitations).
- `sample_output.sexpr` — a small sample of the raw `-sexprinfo` input,
  for inspecting the format without rebuilding Megalodon.
- `APPENDIX.md` — reference for every tag in the `-sexprinfo` format
  (`THM`, `DELTA`, `TLAM`, `PPFAP`, `PTMAP`, …): what each stands for,
  its argument layout, the three separate variable namespaces, the
  primitive table, and the correspondence with Proofgold `.pfg`
  documents. Taken from Megalodon's own emitters, and checked complete
  against all 27 exported corpus files.

Reverse direction and hash checking:

- `lean_export.lean` — Lean metaprogram that dumps each translated
  declaration's *elaborated* `Expr`. Reading what Lean made of the source,
  rather than our own data or the text we emitted, is what makes Lean an
  independent witness.
- `reverse_translate.py` — Lean `Expr` back to Megalodon s-expressions,
  re-splitting Lean's single `bvar` namespace into Megalodon's `TPVAR` /
  `DB` / `HYP`. Compares against the original export; `--emit` writes the
  reconstruction out for hashing.
- `hashcheck.ml` — recomputes content hashes with Megalodon's own
  `Syntax.ptm_all_id` / `ptm_lam_id`, so nothing is reimplemented.
- `compare_hashes.py` — compares those against the ids in the original
  export.
- `hash_negative_control.py` — perturbs each reconstructed term and
  confirms the hash changes, so "every hash matched" is not vacuous.

Corpus access:

- `export_mglib.sh` — exports the mgwiki library, turning `$I` comments
  into `-I` flags and chaining `-ind` / `-owned` in dependency order.
- `resolve_sigs.py` — for a file that fails on an unknown id, finds which
  signature files it needs by iterating on the failures.

## Reproducing

```bash
# 1. build the patched Megalodon
git clone https://github.com/ai4reason/Megalodon /tmp/megalodon-src
cd /tmp/megalodon-src
git apply /path/to/pf_to_sexpr.patch
./makeopt              # needs ocaml/ocamlopt/ocamllex on PATH

# 2. export the corpus
bin/megalodon -sexprinfo /path/to/100thms_12.mg > corpus.sexpr

# 3. translate and verify
python3 sexpr_translate.py corpus.sexpr verified_output/
lean -D maxErrors=20000 verified_output/All.lean   # should print nothing
```

## Known rough edges (not blocking correctness, worth cleaning up)

- Generated names are opaque (`x144`, `h91`, `T21`) rather than
  Megalodon's original binder names — cosmetic, produces some harmless
  unused-variable lint warnings, doesn't affect verification.
- Category boundaries reuse the tactic-based translator's vocabulary
  heuristic (`DOMAIN`/`PROP_VOCAB` regexes), applied to each theorem's
  name, translated statement, and cited dependency names rather than its
  original Megalodon proof text. Close to the old translator's category
  sizes but not identical — heuristic, not exact, same as the original.
- No automated prune-on-error loop yet; today's fixes were each found
  and fixed by hand from a single full-corpus compile's error output.
  For a corpus this well-behaved that was fast enough, but a real
  prune loop (matching the tactic-based translator's `verify_and_prune`)
  would be the right thing before pointing this at a much larger corpus.
- `set_option maxRecDepth 8000` is set globally because two theorems
  needed it; a per-theorem `set_option ... in` would be more precise.
- Of the 31 files in the mgwiki library (`mglib/`), **26 now export and 5
  cannot be done with any public Megalodon source.** Earlier notes here
  said these files could not be checked at all without "the wiki's own
  canonical index export or the specific historical Megalodon build."
  That was mostly wrong, and the correction is in `export_mglib.sh`:

  * The `(** $I sig/X.mgs **)` comments are **not** read by Megalodon.
    The wiki's own `bin/megalodonw.pl` greps them and passes them as `-I`
    flags (and `$T` as a theory flag). Doing the same is most of what was
    missing.
  * Identifiers established by earlier files are supplied as `-ind` plus
    `-owned`, written by earlier runs with `-indout` / `-ownedout`.
  * **Argument order matters.** `-ind`/`-owned` must precede `-I`, because
    `-I` processes the signature file as soon as it is parsed and needs
    the index already loaded. The wrong order fails with "The given id ...
    for `exactly1of2` is not a known index for a term", which reads like a
    missing-index problem rather than an argument-order one -- this cost
    the most time of anything here.

  `Part2`…`Part14` each need `sig/Part1.mgs`…`sig/Part(N-1).mgs`. Their
  declaration names do not overlap at all (1600 distinct names across the
  chain, zero redeclarations), so the per-file exports concatenate into one
  cumulative corpus, which is what the results table above reports.

  The 5 remaining files, and why they are genuinely blocked:

  * `mmset_frege53c`, `mmset_idi` declare `$T setmm` and need a `-setmm`
    flag that Megalodon 1.12 does not have.
  * `NoInitialMonoid`, `AdjForgetBij`, `AdjForgetIrrPartOrd` reference
    `exactly1of3` (`d2a0e453…`). It appears in `sig/PfgE*Preamble*.mgs`,
    but those signature files themselves fail on `exactly1of2`, and
    `resolve_sigs.py` -- which adds signature files on demand, driven by
    each failure, rather than guessing -- exhausts all 26 of them without
    placing it.

  `mgw_test/bin/megalodon` checks all five, but it is **newer than any
  public source**: the GitHub mirror's latest commit is 2024-04-14
  ("Megalodon 1.12 imported from the tarball") and the wiki committed that
  binary on 2026-02-11. It is not carrying a larger index table either --
  its own `-indout` dump is 45 lines -- so it resolves these declarations
  by different logic. Reproducing that needs the newer source, which is not
  published anywhere reachable.

- The large `topology*.mg` files are self-contained and export, but they
  are a different scale: `topology-ax.mg` took 23 minutes to export and
  produced 90 MB of proof terms for 621 theorems.
  `topology_begin_wout_woax_wpreamble.mg` (933 theorems, 44 MB) is through
  the full pipeline and is in the results table above. `topology.mg` is
  369k lines against 45k for the reference corpus and has not been
  attempted; `topology-better-todo.mg` likewise.

## What this doesn't replace yet

This is a second, independent translator, not a drop-in replacement for
`megalodon_full.py` — it matches its output layout (`All.lean` plus
per-category files, all compiling standalone, without the older
translator's known cross-category gap), and it no longer only handles
self-contained input: `export_mglib.sh` chains the mgwiki library. It
still lacks the automated prune-on-error loop, which has not been needed
because nothing has failed to translate, but would be the right thing
before pointing this at a corpus that does not already check.

What remains genuinely open, in rough order of how much it would be worth
doing:

- **`topology.mg` and `topology-better-todo.mg`** (369k and 364k lines).
  These are an order of magnitude past anything here and would be the
  real scaling test. `topology-ax.mg` exports (621 theorems, 23 minutes,
  90 MB of proof terms) but has not been put through Lean.
- **The 5 mgwiki files that need a newer Megalodon** than any published
  source — 2 for `-setmm`, 3 for declarations that exist only in the
  canonical index. Asking upstream for the build behind
  `mgw_test/bin/megalodon` would settle it in one message.
- **The Proofgold document hash.** `pfg/100thms_12.mg.pfg` opens with
  `Document 29c988c5e6c620410ef4e61bcfcbe4213c77013974af40759d8b732c07d61967`,
  a commitment over all 999 theorems published by a third party.
  Reproducing *that* from Lean-derived proofs — by emitting `.mg` with
  Megalodon's `Exact` tactic, which runs the full `check_pf` kernel check,
  and running unmodified Megalodon with `-pfg` — would add a second
  independent kernel to the loop and an externally published number to
  compare against. Everything the per-declaration hash check establishes
  is a prerequisite for it; it is the obvious next step and is not done.
- **Soundness of the Lean axiomatisation**, which no amount of
  round-tripping addresses (see "What this does and does not establish").
