module
public meta import Human.Import.NativeRamProducts
public meta import Lean

public meta section

namespace Airbender.InitsTeardowns.Native.Proofs
open Lean Elab Command

private partial def wiringSyntax : Tree → CommandElabM (TSyntax `term)
  | .pair _ _ _ => `(Tree.Follows.pair (by decide +kernel))
  | .product _ left right => do
    `(Tree.Follows.product (by decide +kernel) $(← wiringSyntax left) $(← wiringSyntax right))
  | .copy _ input => do
    `(Tree.Follows.copy (by decide +kernel) $(← wiringSyntax input))

/-- Emit the constructor proof for the separately transcribed dependency tree. -/
elab "prove_ram_product_wiring " terminal:ident initial:ident " for " data:ident
    " from " path:str inline:(" unified_inline")? : command => do
  let text ← IO.FS.readFile path.getString
  let circuit : Circuit ← match Lean.Json.parse text >>= fromJson? with
    | .ok circuit => pure circuit
    | .error error => throwError "Native initialization JSON: {error}"
  let flavor := if inline.isSome then Extract.Flavor.unified else .standalone
  let artifact ← match Extract.extract flavor circuit with
    | .ok artifact => pure artifact
    | .error error => throwError "Native initialization extraction: {error}"
  elabCommand (← `(theorem $terminal : Tree.Follows ($data).gates ($data).terminal :=
    $(← wiringSyntax artifact.terminal)))
  elabCommand (← `(theorem $initial : Tree.Follows ($data).gates ($data).initial :=
    $(← wiringSyntax artifact.initial)))

end Airbender.InitsTeardowns.Native.Proofs
