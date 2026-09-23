# sexprinfo prototype: proof-term export from Megalodon

This is reconnaissance for the structural rewrite described in the main
README's "Where this goes next" section: translating from Megalodon's own
structured, typed, de-Bruijn, content-addressed export instead of hand-parsed
`.mg` surface text.

## What's here

- `pf_to_sexpr.patch` — a one-line patch against upstream Megalodon
  (`https://github.com/ai4reason/Megalodon`, `src/megalodon.ml`) that wires
  the *already-existing* `pf_to_sexpr` function (in `src/syntax.ml`) into the
  `-sexprinfo` output. Upstream's `-sexprinfo` only emits each theorem's
  *statement* (`THM ...`); this patch adds a `PROOF "<name>" <sexpr>` line
  with the actual checked, optimized proof term at the point each `Qed`
  succeeds.
- `megalodon.ml.patched` — the full file with the patch applied, for
  reference.
- `sample_output.sexpr` — the first ~500KB of `-sexprinfo` output on
  `100thms_12.mg` with the patch applied, so the format can be inspected
  without rebuilding anything.

## What's confirmed working

Built and run against the full 999-theorem reference corpus:

```
theorems: 999   THM entries: 999   PROOF entries: 999   stderr: empty
```

Every theorem, including all 593 surreal-number theorems (the deep
`SNo_rec_i`/`PNo` recursion that caused most of the failures the main
translator still has), exports a complete, well-typed proof term. Example:

```
(PROOF "andI" (TLAM (PROP) (TLAM (PROP) (PLAM (DB 1) (PLAM (DB 0)
  (TLAM (PROP) (PLAM (IMP (DB 2) (IMP (DB 1) (DB 0)))
    (PPFAP (PPFAP (HYP 0) (HYP 2)) (HYP 1)))))))))
```

`TLAM`/`PLAM` (type/prop lambda, i.e. intro), `PPFAP` (modus ponens, i.e.
elim), `HYP n` (hypothesis by de Bruijn position), `KNOWN <hash>` (a cited
fact by content hash, not by name) — a small, closed set of constructors,
no surface syntax, no notation, no precedence. This is the natural-deduction
term form that maps close to one-for-one onto Lean 4 terms.

## Reproducing

```bash
git clone https://github.com/ai4reason/Megalodon /tmp/megalodon-src
cd /tmp/megalodon-src
git apply /path/to/pf_to_sexpr.patch
./makeopt              # needs ocaml/ocamlopt/ocamllex on PATH
bin/megalodon -sexprinfo path/to/100thms_12.mg > out.sexpr
```

## What's NOT done yet

This is data-source reconnaissance only. Building the actual new translator
(consuming this format and emitting Lean 4 syntax) is a separate, substantial
piece of work — a new front end reading `PARAM`/`DEF`/`AXIOM`/`THM`/`PROOF`
records, and a new backend mapping `tm`/`pf` constructors onto Lean 4 terms.
Not attempted here.
