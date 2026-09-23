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

Also includes a statement-level round-trip check (`audit_hash_consistency`):
Megalodon content-addresses every declaration, so two declarations it
considers definitionally identical share a hash — the reference corpus has
8 such pairs (e.g. `pair_Sigma` and `lamI`). The translator verifies all 8
are structurally identical at the raw s-expression level, and refuses to
run if it ever finds a real mismatch, rather than silently trusting that
"Lean accepted it" is the same thing as "it's the right statement."

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
(`DB`/`Ap`/`Lam`/`Imp`/`All` for terms; `Hyp`/`Known`/`PLam`/`PPfAp`/
`PTmAp`/`TLam`/`PTpLam`/`PTpAp` for proofs), each theorem's proof
referencing earlier facts by content hash rather than by name. There is
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
- Only tested against files that are fully self-contained, like
  `100thms_12.mg` itself. Most files in the wider mgwiki library
  (`mglib/`) are fragments that depend on a shared cross-file index or
  `$I`-included signature files; Megalodon itself rejects running them
  standalone (fails at the export step, before this translator ever
  runs), independent of anything in this translator. Confirmed on two
  such files (`NoInitialMonoid.mg`, `TwoRamseyProp_3_5_14.mg`) — both
  fail identically on `ordsucc`'s expected content hash not being
  pre-registered.

  **This is fixable in principle, and partially demonstrated working:**
  Megalodon has a real, built-in mechanism for exactly this
  (`-indout <file>` writes an index of everything a file establishes;
  `-ind <file>` loads it so a later file can reference those hashes).
  Tested directly: building an index from `100thms_12.mg` and feeding it
  to `NoInitialMonoid.mg` moved its failure point forward by 96 lines
  (from `ordsucc` to a later identifier, `pack_b`); tracing `pack_b` to
  its source (`sig/PfgEAug2022Preamble.mgs`) and adding it moved the
  failure forward again (to line 238). Chasing this further hit a wall
  worth stating plainly: even `sig/Part1.mgs`, the most foundational file
  in the wiki's own signature chain with zero declared includes, fails
  the same way on a different identifier (`exactly1of2`) against a
  freshly-built `megalodon` binary. That means these files were checked
  against a canonical index state (a specific deployed instance of the
  wiki, or an older/different build with a larger built-in hash table)
  that a from-source build doesn't reproduce on its own — not something
  more local chaining can fix. Supporting arbitrary mgwiki files would
  need either the wiki's own canonical index export (if one is published
  somewhere) or the specific historical Megalodon build these files were
  authored against, neither of which is available in this environment.
  Supporting a *specific* file or small set of files, where the
  dependency chain is short, is straightforwardly doable with `-ind`/
  `-indout` as demonstrated above.

## What this doesn't replace yet

This is a second, independent translator, not a drop-in replacement for
`megalodon_full.py` — it now matches its output layout (`All.lean` plus
per-category files, all compiling standalone, actually without the older
translator's known cross-category gap), but still lacks the automated
prune-on-error loop and only handles self-contained input files (see
above). Turning it into the project's primary path, and extending it to
the wider mgwiki library, are the next real pieces of work. What's proven
is that the *approach* is not just correct in theory but correct in
practice, on the actual reference corpus, today.
