# Megalodon → Lean 4

A deterministic translator that converts theorems from the
[Megalodon](http://grid01.ciirc.cvut.cz/~chad/megalodon/) proof assistant into
Lean 4, **and machine-checks every result**. Nothing is reported as translated
unless Lean compiled it.

**Update: a second, proof-term-based translator (`sexprinfo-prototype/`)
now verifies 999 / 999 theorems on the same reference corpus — 100%, zero
`sorry`, zero `sorryAx`.** It works from Megalodon's own structured,
already-typed proof export instead of hand-parsed source text, which
removes the whole class of surface-syntax bug the translator below is
still subject to. See `sexprinfo-prototype/README.md` for the full
writeup; it is a second, independent implementation, not yet integrated
as this project's primary path (no category splitting, no prune-on-error
loop yet), so the numbers below still describe what `megalodon_full.py`
itself produces.

On the reference corpus (`100thms_12.mg`, 999 theorems) the translator in
this directory (`megalodon_full.py`, hand-parsed surface syntax +
tactic-script translation) currently produces
**529 verified theorems — 52.9% — with zero `sorry` and zero `sorryAx`.**

---

## Quick start

```bash
# translate + verify (~45 min: it compiles a 999-theorem Lean file repeatedly)
python3 megalodon_full.py 100thms_12.mg --output ./lean_out

# confirm the result independently (~90 s)
./verify_output.sh lean_out
```

Requires Python 3.8+ (standard library only) and Lean 4 on `PATH`
(developed against 4.34.0). No Mathlib, no network, no API keys.

### Options

| Flag | Effect |
|---|---|
| `--no-verify` | translate only, skip Lean. ~1 min. Output is **unverified** |
| `--statements-only` | emit each statement with `sorry` as its proof. Checks that *statements* typecheck; proves nothing |

---

## Results

| Category | verified | of | coverage |
|---|---|---|---|
| Propositional logic | 39 | 39 | **100%** |
| Set theory | 200 | 203 | 99% |
| Natural numbers | 96 | 104 | 92% |
| Ordinals | 49 | 60 | 82% |
| Surreal numbers | 145 | 593 | 24% |
| **Total** | **529** | **999** | **52.9%** |

Of the 529, 526 translated and verified directly; 3 were recovered by the
seeded-proof-search fallback (see stage 7, `recover()`) after their ported
proof failed but the statement still typechecked.

### Recent fixes

Four real, independently-verified translation bugs, each found by tracing an
actual Lean compile error back to its cause rather than guessing:

- **`witness` tactic parenthesization.** Megalodon's `witness t` accepts a
  bare, unparenthesized application (`witness f w`); the translator spliced
  that straight into Lean's `apply _wH f w`, which Lean reads as two curried
  arguments instead of one. Fixed by parenthesizing the witness term. This
  was the single largest fix (first-pass clean theorems roughly doubled).
- **A `sorryAx` leak in the recovery fallback.** The seeded-proof-search
  recovery step could hint `solve_by_elim` with a lemma name that had
  already been deleted for failing elsewhere. Citing a nonexistent name
  inside a hint list doesn't reliably surface as a hard compile error in
  Lean 4 — it can silently degrade to a hidden placeholder instead, which
  only showed up in the axiom audit (`sorryAx` present) rather than as a
  compile failure. Fixed by restricting recovery hints to names that
  actually survived pruning.
- **Nested-tuple misdetection.** `(A, fun x => B)` — a Megalodon pair whose
  component contains a lambda — was being left untranslated as Lean's
  native tuple type instead of Megalodon's own set-encoded pair, because the
  heuristic that guards against ambiguous binder commas matched `fun`
  anywhere in a part, even when safely nested inside its own parens. Fixed
  by making that check depth-aware.
- **Primed identifiers in typed `intro`.** `intro Hw': w' :e L` (Megalodon's
  inline type-ascription form) was supposed to have its type annotation
  stripped before reaching Lean, but the stripping regex's character class
  didn't include the apostrophe, so primed names like `Hw'` never matched
  and the invalid syntax leaked straight through.

Verified means: the file compiles under Lean with no errors, contains no
`sorry`, and `#print axioms` shows no `sorryAx`. The only axioms used are
Megalodon's own — `Empty`, `Union`, `Power`, `Repl`, `Eps_i`, `In_ind`,
`set_ext`, `func_ext`, `prop_ext` and friends. Nothing is assumed that
Megalodon does not itself assume.

### Output layout

```
lean_out/
  Prelude.lean      definitions, axioms and notation, translated
  All.lean          every verified theorem, once, in source order -- authoritative
  prop_logic.lean   per-category files (see Limitations: not all compile standalone yet)
  set_theory.lean
  nat_arith.lean
  ordinals.lean
  surreals.lean
```

Each category file carries the cross-category lemmas its proofs cite, marked
`-- dependency from <category>`, plus only the prelude declarations those
proofs reach. **`All.lean` is authoritative**: per-category files repeat
borrowed lemmas, so their theorem counts sum to more than 529.

---

## How it works

Eight stages, all in `megalodon_full.py`:

1. **Parse** (`parse_source`) — read the `.mg` file into structured records,
   and reconstruct the `Section`/`Variable` scoping Megalodon leaves implicit.
2. **Learn the notation** (`build_token_map`, `build_binder_ops`,
   `build_setlam`) — Megalodon *declares* its own operators, so the translator
   reads those declarations rather than hardcoding a table.
3. **Translate expressions** (`Converter.expr`) — set-builders, bounded
   quantifiers, set-lambdas, tuples, numerals, if-then-else.
4. **Emit the prelude** (`prelude_items`) — every definition and axiom as Lean.
5. **Translate proofs** (`translate_tactics`) — term proofs carry over
   directly; tactic scripts are mapped tactic by tactic.
6. **Categorise** (`categorise`) — sort theorems into five groups by the
   vocabulary they use.
7. **Verify and prune** (`verify_and_prune`) — compile all theorems in one
   source-ordered file, delete whatever Lean rejects, recompile, repeat.
8. **Split** — write per-category files, each recompiled to prove it stands
   alone.

Stage 7 is the heart of it: **the output is what survived Lean, not what the
translator produced.**

### Translation notes

Megalodon and Lean disagree in ways that are easy to get subtly wrong:

- **Operators collide.** Lean already owns `/\`, `\/`, `<->`, `=`. Every
  Megalodon operator is remapped to a token Lean cannot already mean
  (`⋏`, `⋎`, `∊`, or a generated `⋄N⋄`).
- **Precedence is inverted.** Megalodon binds *tighter* with a *lower* number;
  Lean is the opposite. `lean_prec` maps `n → 1100 - n`.
- **Conjunction is left-associative** (`Infix /\ 780 left`), so `A /\ B /\ C`
  is `(A/\B)/\C`. Guards attached to bounded quantifiers must be bracketed
  against the body or they swallow its first conjunct.
- **The logic is Church-encoded.** Megalodon defines its own `and`, `or`,
  `not`, `False` rather than using built-ins, and its proofs exploit those
  definitions. They are translated as definitions, not mapped onto Lean's.
- **`=` is Leibniz equality** — `forall Q, Q x y -> Q y x` — and proofs
  *apply* an equation like a function. The notation binds to Lean's `Eq` so
  `rw` works, and a `CoeFun` instance restores the Leibniz use.
- **Sets are applicable.** `u 0` means `ap u 0`; Megalodon declares this with
  `Notation SetImplicitOp ap`, and it becomes a Lean `CoeFun` instance.
- **Numerals are sets.** `0` is `Empty`, `n+1` is `ordsucc n`.
- **The default sort is `set`.** A bare `forall x` means `forall x : set`.
- **Nested syntax needs scanners, not regexes.** Bracket-counting scanners
  handle binders, `if/then/else`, tuples and proof blocks; regular expressions
  cannot match nested brackets.

---

## Limitations

- **Surreal numbers are 24%**, and account for 448 of the 470 failures.
  Individually traced proofs in this category commonly mix several distinct
  translation issues in one long tactic script (a single 1,300-line proof
  was found to trigger five different error types), rather than one shared
  root cause, so each further gain here costs proportionally more than the
  fixes above did.
- **22 non-surreal theorems fail**, most independently rather than as a
  cascade from a single surreal dependency.
- **Positional rewriting is partial.** `rewrite H at 2` maps to Lean's
  occurrence-selective `rw`, but some goal-state divergences remain.
- **Categories are heuristic.** Theorems are filed by the vocabulary they use;
  the boundaries are approximate, though no longer a catch-all bucket.
- **Per-category files do not all compile fully standalone yet.** `All.lean`
  is the authoritative, fully verified output. The per-category split
  (stage 8) is known to miss some cross-category dependencies for a handful
  of theorems in the larger categories — a real, pre-existing gap in the
  splitting logic, not in the underlying proofs, which are only ever counted
  as verified based on `All.lean`.

Failures are never hidden: a theorem that does not compile is removed from the
output entirely, so no file contains an unproved claim.

### Where this goes next

**Update: done, and it worked.** This translator works from Megalodon's
surface `.mg` text, hand-parsed with bracket-counting scanners (see "Nested
syntax needs scanners, not regexes" above) — a real source of risk
(precedence, notation, binder edge cases), and the root cause of every bug
fixed in the "Recent fixes" section. The natural fix was to translate from
Megalodon's own typed, de-Bruijn, content-addressed proof export
(`-sexprinfo`) instead, as proof terms rather than tactic scripts. That's no
longer a proposal: `sexprinfo-prototype/` is a second, working translator
built exactly this way, and it verifies **999/999 theorems (100%)** on this
same reference corpus, including the entire surreal-number category that is
this translator's persistent weak point. See `sexprinfo-prototype/README.md`
for the full result and how to reproduce it.

What's left is integration, not proof-of-concept: category splitting, a
proper prune-on-error loop, and readable generated names, so it can replace
`megalodon_full.py` as this project's primary path rather than sit alongside
it. Tracked as the next real piece of work.

---

## Files

This directory holds two independent translators against the same
reference corpus — see "Where this goes next" above for how they compare.

| File | Purpose |
|---|---|
| `megalodon_full.py` | the surface-text, tactic-script translator (529/999) |
| `verify_output.sh` | independent verification and axiom audit, for `megalodon_full.py`'s output |
| `100thms_12.mg` | reference corpus, 999 theorems, shared by both translators |
| `sexprinfo-prototype/` | the proof-term translator (999/999) — see its own README for its files |

---

## Verifying the claims yourself

**`megalodon_full.py`'s result (529/999):**

```bash
python3 megalodon_full.py 100thms_12.mg --output ./lean_out
./verify_output.sh lean_out
```

Compiles every generated file with `lean -D maxErrors=20000`, checks each for
`sorry`, then runs `#print axioms` over every theorem and fails loudly on
`sorryAx`. A `sorry` compiles cleanly and proves nothing — that check is the
one that matters.

Note: the in-file `set_option maxErrors` is ignored by Lean; the limit must be
passed on the command line, or Lean stops after 100 errors and an incomplete
run can look like a successful one.

**`sexprinfo-prototype`'s result (999/999):**

```bash
lean -D maxErrors=20000 sexprinfo-prototype/verified_output/All.lean
# or any one category standalone, e.g.:
lean -D maxErrors=20000 sexprinfo-prototype/verified_output/surreals.lean
```

Should print nothing. Full reproduction from source (rebuilding the patched
Megalodon binary, regenerating the export, re-running the translator) and the
axiom-audit command are in `sexprinfo-prototype/README.md`.
