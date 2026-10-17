import Airbender.Import.SetupEmbed
import Lean.AddDecl

namespace Airbender.Setup.Proofs
open Lean Elab Command

private def arrayHalf (value : Lean.Expr) (right : Bool) : CommandElabM Lean.Expr := do
  unless value.getAppFn.isConstOf ``Array.append do
    throwError "block partition requires the imported balanced append tree"
  let args := value.getAppArgs
  unless args.size == 3 do throwError "unsupported imported append arity"
  return args[if right then 2 else 1]!

/-- Name one exact subtree at a bounded depth of the imported block array. -/
elab "column_block_part " name:ident " from " column:ident " depth " depth:num
    " part " part:num : command => do
  let d := depth.getNat
  unless d ≤ 8 && part.getNat < 2 ^ d do throwError "invalid imported block partition"
  let sourceName ← resolveGlobalConstNoOverload column
  let info ← getConstInfoDefn sourceName
  unless info.type.isConstOf ``Airbender.Setup.Column &&
      info.value.getAppFn.isConstOf ``Airbender.Setup.Column.mk do
    throwError "block partition requires an imported literal Column"
  let args := info.value.getAppArgs
  unless args.size == 1 do throwError "unsupported imported Column constructor"
  let mut value := args[0]!
  for level in [:d] do
    value ← arrayHalf value (part.getNat / 2 ^ (d - 1 - level) % 2 == 1)
  let type := mkApp (mkConst ``Array [Level.zero]) (mkConst ``Airbender.Setup.Block)
  let height := getMaxHeight (← getEnv) value + 1
  let fullName := (← getCurrNamespace) ++ name.getId
  liftCoreM <| addAndCompile (.defnDecl {
    name := fullName, levelParams := [], type, value,
    hints := .regular height, safety := .safe })

end Airbender.Setup.Proofs
