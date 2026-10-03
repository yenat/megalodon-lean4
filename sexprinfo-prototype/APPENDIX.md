# Appendix: the `-sexprinfo` vocabulary

Every tag that appears in a Megalodon `-sexprinfo` export, what it stands
for, and what its arguments mean. Transcribed from the emitters in
Megalodon's own source (`src/syntax.ml`: `tp_to_sexpr`, `tm_to_sexpr`,
`pf_to_sexpr`; `src/megalodon.ml` for the top-level forms), not from
observation of the corpus, so the lists below are complete rather than
"everything we happened to see."

This is the format `sexpr_translate.py` reads and `reverse_translate.py`
writes back.

## The four languages

An export is a sequence of **top-level forms**, one per line. Inside them,
three distinct and non-interchangeable languages appear:

| | what it describes | tags |
|---|---|---|
| `tp` | simple types | `TPVAR` `PROP` `SET` `AR` |
| `tm` | terms, including propositions | `DB` `TMH` `PRIM` `TPAP` `AP` `LAM` `IMP` `ALL` |
| `pf` | proofs | `HYP` `KNOWN` `PTPAP` `PTMAP` `PPFAP` `PLAM` `TLAM` |

Keeping them apart matters: a proposition is a `tm` (so `(PROP)` and a
specific proposition are different kinds of thing), and `IMP`/`ALL` live in
`tm` while their proof-level counterparts `PLAM`/`TLAM` live in `pf`.

## Top-level forms

Field order is exactly as emitted. `<hash>` is a 64-character hex content
id, always quoted.

| form | fields | meaning |
|---|---|---|
| `(PRIM i "name" "hash" tp)` | index, name, id, type | a primitive constant of the theory (see the table below) |
| `(PARAM "name" "hash" i tp)` | name, id, arity, type | an opaque declared constant — `Parameter` in `.mg` |
| `(DEF "name" "hash" i tp tm)` | name, id, arity, type, body | a definition; the id denotes the **body**, not the type |
| `(AXIOM "name" "hash" i tm)` | name, id, arity, proposition | an assumed proposition; the id denotes the **proposition** |
| `(THM "name" "ahv" "pfgahv" i tm)` | name, prop id, Proofgold prop id, arity, proposition | a proved proposition |
| `(DELTA "hash")` | id | one definition whose unfolding the following proof depends on — the proof's *delta set*, emitted once per element before the proof |
| `(USESKNOWN "hash")` | id | emitted by the proof **checker**, once each time it resolves a `KNOWN` reference while checking. A usage trace, not part of any declaration's structure, and by far the most numerous line in an export — 31,996 of them in the 999-theorem reference corpus |
| `(PROOF "name" pf)` | name, proof term | the checked proof term. **Added by `pf_to_sexpr.patch`**; upstream `-sexprinfo` does not emit it |
| `(QED)` | — | the preceding proof completed |
| `(QEDWITHADMITS)` | — | completed, but with admitted subgoals |
| `(ADMITTED)` | — | the theorem was admitted, not proved |

`USESKNOWN` deserves a note, because it is the one line here that is not a
declaration. It comes from `check_pf` in `src/syntax.ml` rather than from
the declaration printer, is interleaved with everything else as checking
proceeds, and repeats the same id as often as the proof cites it. A reader
of the format should skip it; it carries no information the `PROOF` term
does not already contain. (It is emitted at each polymorphic arity 0–6,
which is why there are seven identical `Printf` sites.)

Three more forms appear only under `-sexprallsubgoals`, describing the
context of an open goal rather than a finished declaration:
`(VAR "name" tp)`, `(LET "name" tp tm)`, `(HYP "name" tm)` and `(GOAL tm)`.
Note that `HYP` here is a *top-level* form naming a context hypothesis, and
is unrelated to the `pf`-level `(HYP i)` below.

### `i` — the arity field

The integer on `PARAM`, `DEF`, `AXIOM` and `THM` is the number of **type
variables** the declaration abstracts over. It is *not* a binder in the
type or body: a polymorphic declaration's `tp`/`tm` simply mentions
`(TPVAR 0)`, `(TPVAR 1)`, … and the count lives here. So `eq` is

```
(DEF "eq" "5a6af35f…" 1 (AR (TPVAR 0) (AR (TPVAR 0) (PROP))) (LAM (TPVAR 0) …))
```

with arity `1` and no binder for the type variable. Translating to a system
that *does* bind type parameters — Lean's `def eq (T : Type) …` — means
introducing those binders on the way out and peeling them on the way back.

### `ahv` versus `pfgahv`

A `THM` carries two ids. `ahv` is Megalodon's own content id for the
proposition (`Syntax.ptm_all_id`). `pfgahv` is the corresponding Proofgold
proposition id (`pfg_propid`), which is what appears in the `.pfg`
documents and on the Proofgold blockchain. They are different hashes of the
same proposition under different conventions.

There is **no proof id.** `Syntax.ppf_id` exists but is stubbed to return
all zeros, with the comment that it "isn't really needed anymore and is
expensive to compute." Megalodon content-addresses propositions and
objects, not proof terms.

## Types (`tp`)

| tag | expansion | meaning |
|---|---|---|
| `(PROP)` | proposition | the type of propositions |
| `(SET)` | set | the type of sets, the theory's base domain |
| `(AR a b)` | **ar**row | the function type `a -> b` |
| `(TPVAR i)` | **t**y**p**e **var**iable | type variable `i`, counted from the **outermost**, 0-based — an absolute position, *not* a de Bruijn index |

## Terms (`tm`)

| tag | expansion | meaning |
|---|---|---|
| `(DB i)` | **d**e **B**ruijn | variable bound by the `i`-th enclosing `LAM`/`ALL`, counting from the innermost, 0-based |
| `(TMH "hash")` | **t**er**m** **h**ash | reference to a previously declared object by content id |
| `(PRIM i)` | **prim**itive | primitive constant `i` |
| `(AP f a)` | **ap**plication | `f a` |
| `(TPAP f a)` | **t**y**p**e **ap**plication | instantiation of a polymorphic object at type `a` |
| `(LAM a m)` | **lam**bda | `fun x : a => m` |
| `(IMP p q)` | **imp**lication | `p -> q`. Binds nothing |
| `(ALL a p)` | for **all** | `forall x : a, p` |

`IMP` binding nothing is worth stating twice, because systems that
represent implication as a degenerate dependent function — Lean's
`forallE` — *do* spend a binder on it, and indices have to be realigned
across that difference.

## Proofs (`pf`)

Seven constructors, and that is all of them.

| tag | expansion | proves | corresponds to |
|---|---|---|---|
| `(HYP i)` | **hyp**othesis | the `i`-th enclosing `PLAM`'s proposition, innermost 0-based | using an assumption |
| `(KNOWN "hash")` | known fact | the proposition with that id | citing an earlier theorem or axiom |
| `(PLAM p d)` | **p**roof **lam**bda | `p -> q`, where `d` proves `q` under `p` | implication introduction |
| `(TLAM a d)` | **t**erm **lam**bda | `forall x : a, q` | universal introduction |
| `(PPFAP d e)` | **p**roof–**p**roo**f** **ap**plication | `q`, from `d : p -> q` and `e : p` | modus ponens |
| `(PTMAP d m)` | **p**roof–**t**er**m** **ap**plication | `q[m/x]`, from `d : forall x:a, q` | universal instantiation |
| `(PTPAP d a)` | **p**roof–**t**y**p**e **ap**plication | the proposition at type `a` | instantiating a polymorphic fact |

### `PTPLAM` is not a tag

Readers of Megalodon's internals will have seen `PTpLam`, and an earlier
version of this project's README listed it among the proof constructors.
It is not part of this format and `pf_to_sexpr` cannot emit it: the `pf`
type has the seven constructors above and no type-lambda. Type abstraction
in a proof is carried by the arity integer of the enclosing declaration
(`type ppf = int * pf`) and is materialised as `Mathdata.PTpLam` only
inside the hashing representation. Nothing in a `(PROOF …)` line ever
contains it.

### Three namespaces, one at a time

`TPVAR`, `DB` and `HYP` are three **separate** variable namespaces with
separate numbering. `TLAM` binds a `DB`; `PLAM` binds a `HYP`; the arity
field accounts for `TPVAR`. A system with a single variable namespace — again,
Lean — merges all three, so index arithmetic does not survive a naive
translation in either direction. `andI`, below, is the smallest example
where this is visible.

## Primitive constants (`PRIM i`)

The index order is fixed by `src/megalodon.ml`:

| `i` | name | type | notes |
|---|---|---|---|
| 0 | `Eps` | `((TPVAR 0 -> PROP) -> TPVAR 0)` | polymorphic choice; appears under `TPAP`. Rejected in the `hf` theory |
| 1 | `In` | `(SET -> (SET -> PROP))` | set membership |
| 2 | `Empty` | `SET` | |
| 3 | `Union` | `(SET -> SET)` | |
| 4 | `Power` | `(SET -> SET)` | |
| 5 | `Repl` | `(SET -> ((SET -> SET) -> SET))` | replacement |
| 6 | `UnivOf` | `(SET -> SET)` | Grothendieck universe; `Egal` theory only |

Which primitives are admitted depends on the theory selected by the `$T`
line or a theory flag (`Egal`, the default, `hf`, `mizar`, `hoas`).

In practice a corpus refers to these by content id (`TMH`) rather than by
`PRIM`, because `PRIM i` is hashed to an id on declaration and later
references use that id.

## Normalisation, and what a shared id means

Two declarations with the same id are **not** necessarily structurally
identical. `Syntax.tm_id` hashes the term *after*
`tm_beta_eta_exeq_norm`, which

- contracts beta-redexes (`AP` of a `LAM`),
- contracts eta-redexes (`LAM a (AP f (DB 0))` where `f` does not use `DB 0`),
- unfolds `ex`, `eq` and `neq` — identified by literal hash — where they
  are applied to a type.

So `coarser_than`, defined as `fun A B => Subq A B`, shares `Subq`'s id
while being its eta-expansion; and `True` (a `DEF`, whose id denotes its
body) shares an id with `TrueI` (a `THM`, whose id denotes its
proposition). Any check against these ids has to allow for that.

## Reading one declaration end to end

`andI : forall A B : prop, A -> B -> A /\ B`, as exported:

```
(THM "andI" "7f6246d0…" "3bf1985f…" 0
  (ALL (PROP) (ALL (PROP) (IMP (DB 1) (IMP (DB 0)
    (AP (AP (TMH "87fba1d2…") (DB 1)) (DB 0)))))))
(DELTA "87fba1d2…")
(PROOF "andI"
  (TLAM (PROP) (TLAM (PROP)
    (PLAM (DB 1) (PLAM (DB 0)
      (TLAM (PROP)
        (PLAM (IMP (DB 2) (IMP (DB 1) (DB 0)))
          (PPFAP (PPFAP (HYP 0) (HYP 2)) (HYP 1)))))))))
(QED)
```

The statement: two `ALL (PROP)` bind the propositional variables `A` and
`B`; inside, `(DB 1)` is `A` and `(DB 0)` is `B`. `TMH "87fba1d2…"` is
`and`, applied to both. The `DELTA` line records that checking the proof
requires unfolding `and`.

The proof: two `TLAM` bind `A` and `B` as `DB`s; two `PLAM` assume `A` and
`B` as `HYP`s; then — since `and A B` unfolds to
`forall p:prop, (A -> B -> p) -> p` — a third `TLAM` binds `p` and a third
`PLAM` assumes `A -> B -> p`. The body applies that assumption to the two
earlier ones.

Counting the two namespaces separately is the point. Binders in order are
`A`, `B`, `hA`, `hB`, `p`, `hf`. Among `TLAM`s only, `p` is `DB 0`, `B` is
`DB 1`, `A` is `DB 2`. Among `PLAM`s only, `hf` is `HYP 0`, `hB` is
`HYP 1`, `hA` is `HYP 2`. So `(PPFAP (PPFAP (HYP 0) (HYP 2)) (HYP 1))` is
`hf hA hB`. In Lean the same term is
`(app (app (bvar 0) (bvar 3)) (bvar 2))`, over one merged namespace —
the same proof, different arithmetic.

## Proofgold documents (`.pfg`)

The mgwiki ships a `.pfg` per corpus file (`megalodon -pfg`), the form in
which a document is published to the Proofgold blockchain. Different
surface syntax, same content, prefix rather than parenthesised:

| `.pfg` | `-sexprinfo` |
|---|---|
| `Document <sha>` | — (the document's root commitment) |
| `Base set` | — (declares the base type) |
| `Def`, `Known`, `Thm` | `DEF`, `AXIOM`, `THM` |
| `TpArr`, `Prop`, `set` | `AR`, `PROP`, `SET` |
| `Ap`, `Lam`, `Imp`, `All`, `Prim` | `AP`, `LAM`, `IMP`, `ALL`, `PRIM` |
| `Eq`, `Ex` | sugar for the `eq` / `ex` constants |
| `TmLa`, `PrLa` | `TLAM`, `PLAM` |
| `TmAp`, `PrAp` | `PTMAP`, `PPFAP` |

`.pfg` names its binders (`Lam A Prop …`) where the s-expression form is
nameless, and the `Document` line is a single hash over the whole file —
the externally published number this project does not yet reproduce from
the Lean side.

## Vocabulary this project adds

Neither of these is Megalodon's; both exist to carry data between the
stages of the round trip.

**`lean_export.lean`** emits one line per declaration, holding Lean's
elaborated `Expr` in a parallel s-expression syntax, lower-case to keep it
visually distinct from Megalodon's:

```
(DECL "name" KIND <type-expr> <value-expr>)
```

`KIND` is `AXIOM`, `DEF`, `THM` or `OTHER`; a declaration with no value
has `(none)`. The `Expr` tags mirror Lean's constructors: `bvar`, `fvar`,
`mvar`, `sort`, `const`, `app`, `lam`, `all` (for `forallE`), `letE`,
`lit`, `proj`. `mdata` is dropped rather than represented, since it
carries no term content.

**`hashcheck.ml`** reads the reconstruction back in as:

```
(RECON "name" <kind> <arity> <tm>)
```

where `<kind>` is `all` for a proposition, hashed with
`Syntax.ptm_all_id`, or `lam` for a definition body, hashed with
`Syntax.ptm_lam_id` — the two functions Megalodon itself uses to assign
ids.

## Source

| what | where |
|---|---|
| `tp` / `tm` / `pf` types and emitters | `src/syntax.ml` |
| top-level forms | `src/megalodon.ml` (search `sexprinfo`) |
| the `PROOF` line | `pf_to_sexpr.patch` in this directory |
| id assignment | `Syntax.ptm_all_id`, `ptm_lam_id`, `tm_id`, `tp_id` |
| normalisation | `Syntax.tm_beta_eta_exeq_norm` |
| primitive table | `Syntax.primname` and `src/megalodon.ml` |

Megalodon: <https://github.com/ai4reason/Megalodon> (1.12).
