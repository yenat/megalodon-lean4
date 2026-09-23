# sexprinfo prototype: a complete, working proof-term translator

This started as reconnaissance for translating from Megalodon's own
structured, typed, de-Bruijn, content-addressed export instead of
hand-parsed `.mg` surface text (see the main README's "Where this goes
next"). It is no longer just reconnaissance: `sexpr_translate.py` is a
working translator, built and verified end to end on the same 999-theorem
reference corpus (`100thms_12.mg`) the main translator uses.

## Result

**999 / 999 theorems verified — 100% — with zero `sorry` and zero
`sorryAx`.** Confirmed by both a full recompile of `All_via_sexpr.lean`
and an independent `#print axioms` pass over every theorem. The only
axioms used are Megalodon's own 17 foundational ones (`Empty`, `In_ind`,
`set_ext`, `func_ext`, `prop_ext`, `Eps_i`, `Eps_i_ax`, `UnivOf`, and
similar) — the same axiom set the tactic-based translator's output
depends on, nothing extra assumed.

This includes every theorem in the surreal-number category, which was the
tactic-based translator's persistent weak point (23-24% all day) — here
it's 593/593.

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
- `All_via_sexpr.lean` — the full, verified output: all 999 theorems,
  one file, compiling clean.
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
python3 sexpr_translate.py corpus.sexpr All_via_sexpr.lean
lean -D maxErrors=20000 All_via_sexpr.lean   # should print nothing
```

## Known rough edges (not blocking correctness, worth cleaning up)

- Generated names are opaque (`x144`, `h91`, `T21`) rather than
  Megalodon's original binder names — cosmetic, produces some harmless
  unused-variable lint warnings, doesn't affect verification.
- No per-category split yet (the main translator's `All.lean` /
  `prop_logic.lean` / etc. structure) — everything is one file.
- No automated prune-on-error loop yet; today's fixes were each found
  and fixed by hand from a single full-corpus compile's error output.
  For a corpus this well-behaved that was fast enough, but a real
  prune loop (matching the tactic-based translator's `verify_and_prune`)
  would be the right thing before pointing this at a much larger corpus.
- `set_option maxRecDepth 8000` is set globally because two theorems
  needed it; a per-theorem `set_option ... in` would be more precise.

## What this doesn't replace yet

This is a second, independent translator, not a drop-in replacement for
`megalodon_full.py` — it doesn't yet do category splitting, the
per-category standalone-compile check, or produce the same output layout.
Turning it into the project's primary path is real follow-up work, not
attempted here. What's proven is that the *approach* is not just correct
in theory but correct in practice, on the actual reference corpus, today.
