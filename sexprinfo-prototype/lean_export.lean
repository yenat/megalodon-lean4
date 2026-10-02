/-
Dump every translated declaration's *elaborated* `Expr`, for the reverse
direction of the round trip (`reverse_translate.py`).

Reading Lean's elaborated term, rather than our own intermediate data or
the source text we emitted, is the whole point: it makes Lean an
independent witness. Anything the elaborator did -- inserting an implicit
argument, resolving a precedence differently, normalising a binder type --
shows up here and nowhere else.

This file is an epilogue. It is concatenated after the generated corpus:

    printf 'import Lean\nset_option linter.unusedVariables false\n' > export.lean
    cat verified_output/All.lean lean_export.lean >> export.lean
    MEGALODON_EXPR_OUT=corpus_expr.sexpr lean export.lean
    python3 reverse_translate.py corpus.sexpr corpus_expr.sexpr

`import` has to come first in a Lean file, and `All.lean` has no imports
of its own, so prepending the two lines above is all that is needed.
-/

section MegalodonExprExport
open Lean

private partial def dumpE : Expr → String
  | .bvar i          => s!"(bvar {i})"
  | .fvar id         => s!"(fvar \"{id.name}\")"
  | .mvar id         => s!"(mvar \"{id.name}\")"
  | .sort u          => s!"(sort \"{u}\")"
  | .const n _       => s!"(const \"{n}\")"
  | .app f a         => s!"(app {dumpE f} {dumpE a})"
  | .lam n t b _     => s!"(lam \"{n}\" {dumpE t} {dumpE b})"
  | .forallE n t b _ => s!"(all \"{n}\" {dumpE t} {dumpE b})"
  | .letE n t v b _  => s!"(letE \"{n}\" {dumpE t} {dumpE v} {dumpE b})"
  | .lit _           => s!"(lit)"
  | .mdata _ e       => dumpE e
  | .proj s i e      => s!"(proj \"{s}\" {i} {dumpE e})"

open Elab Command in
run_cmd do
  let env ← getEnv
  let path := (← IO.getEnv "MEGALODON_EXPR_OUT").getD "expr_dump.sexpr"
  IO.FS.withFile path .write fun h => do
    for (n, ci) in env.constants.toList do
      if n.getPrefix == `Megalodon && !n.isInternal then
        let kind := match ci with
          | .axiomInfo _ => "AXIOM"
          | .defnInfo _  => "DEF"
          | .thmInfo _   => "THM"
          | _            => "OTHER"
        -- `ConstantInfo.value?` does not expose theorem proofs in Lean
        -- 4.34, so the value is taken from the constructor directly.
        let val := match ci with
          | .thmInfo v  => dumpE v.value
          | .defnInfo v => dumpE v.value
          | _           => "(none)"
        h.putStrLn s!"(DECL \"{n.getString!}\" {kind} {dumpE ci.type} {val})"
end MegalodonExprExport
