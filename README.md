# Megalodon → Lean 4

A deterministic translator that converts theorems from the
[Megalodon](http://grid01.ciirc.cvut.cz/~chad/megalodon/) proof assistant into
Lean 4, **and machine-checks every result**. Nothing is reported as translated
unless Lean compiled it.

On the reference corpus (`100thms_12.mg`, 999 theorems) it currently produces
**500 verified theorems — 50.0% — with zero `sorry` and zero `sorryAx`.**

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
| Set theory | 189 | 203 | 93% |
| Natural numbers | 87 | 104 | 84% |
| Ordinals | 46 | 60 | 77% |
| Surreal numbers | 139 | 593 | 23% |
| **Total** | **500** | **999** | **50.0%** |

Verified means: the file compiles under Lean with no errors, contains no
`sorry`, and `#print axioms` shows no `sorryAx`. The only axioms used are
Megalodon's own — `Empty`, `Union`, `Power`, `Repl`, `Eps_i`, `In_ind`,
`set_ext`, `func_ext`, `prop_ext` and friends. Nothing is assumed that
Megalodon does not itself assume.

### Output layout

```
lean_out/
  Prelude.lean      definitions, axioms and notation, translated
  All.lean          every verified theorem, once, in source order
  prop_logic.lean   per-category files, each compiling standalone
  set_theory.lean
  nat_arith.lean
  ordinals.lean
  surreals.lean
```

Each category file carries the cross-category lemmas its proofs cite, marked
`-- dependency from <category>`, plus only the prelude declarations those
proofs reach. **`All.lean` is authoritative**: per-category files repeat
borrowed lemmas, so their theorem counts sum to more than 500.

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

- **Surreal numbers are 23%**, and account for 454 of the 499 failures.
  They rest on a deep recursion stack (`SNo_rec_i`, `SNo_rec2`, `PNo`) where
  individual proof-level mismatches remain.
- **45 non-surreal theorems fail**, of which about two-thirds depend on a
  surreal lemma that itself fails.
- **Positional rewriting is partial.** `rewrite H at 2` maps to Lean's
  occurrence-selective `rw`, but some goal-state divergences remain.
- **Categories are heuristic.** Theorems are filed by the vocabulary they use;
  the boundaries are approximate, though no longer a catch-all bucket.

Failures are never hidden: a theorem that does not compile is removed from the
output entirely, so no file contains an unproved claim.

---

## Files

| File | Purpose |
|---|---|
| `megalodon_full.py` | the translator (single file, standard library only) |
| `verify_output.sh` | independent verification and axiom audit |
| `100thms_12.mg` | reference corpus, 999 theorems |

---

## Verifying the claims yourself

```bash
./verify_output.sh lean_out
```

Compiles every generated file with `lean -D maxErrors=20000`, checks each for
`sorry`, then runs `#print axioms` over every theorem and fails loudly on
`sorryAx`. A `sorry` compiles cleanly and proves nothing — that check is the
one that matters.

Note: the in-file `set_option maxErrors` is ignored by Lean; the limit must be
passed on the command line, or Lean stops after 100 errors and an incomplete
run can look like a successful one.
