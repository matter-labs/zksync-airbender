import Airbender.Proofs.GKRProtocol.BlockNormalization
import Airbender.Proofs.Tables.BlockSlices

namespace Airbender.Compiler.BlockPartsImport
open Lean Elab Command
set_option warningAsError true

private partial def blockArray (value : Lean.Expr) : CommandElabM (Array Lean.Expr) := do
  let value := value.consumeMData
  if let .const name _ := value then
    return ← blockArray (← getConstInfoDefn name).value
  if value.getAppFn.isConstOf ``Array.append then
    let arguments := value.getAppArgs
    unless arguments.size == 3 do throwError "unexpected block array append"
    return (← blockArray arguments[1]!) ++ (← blockArray arguments[2]!)
  unless value.getAppFn.isConstOf ``List.toArray do throwError "expected literal block array"
  let arguments := value.getAppArgs
  unless arguments.size == 2 do throwError "unexpected literal block array"
  Setup.Proofs.literalList arguments[1]!

/-- Name an unchanged span of the actual imported block expressions. A later
kernel proof checks its relation to the source column and opposite encoding. -/
elab "column_blocks_part " name:ident " from " column:term " start " first:num " stop " last:num : command => do
  let expanded ← liftTermElabM do
    let value ← Term.elabTermEnsuringType column (mkConst ``Setup.Column)
    Meta.withTransparency .all (Meta.whnf value)
  unless expanded.getAppFn.isConstOf ``Setup.Column.mk do throwError "expected an imported column"
  let blocks ← blockArray expanded.getAppArgs[0]!
  let start := first.getNat
  let stop := last.getNat
  unless start ≤ stop && stop ≤ blocks.size do throwError "block proof span is outside its source"
  let selected := blocks.extract start stop
  let element := mkConst ``Setup.Block
  let type := mkApp (mkConst ``List [Level.zero]) element
  let value := selected.foldr (fun block rest =>
    mkApp3 (mkConst ``List.cons [Level.zero]) element block rest)
    (mkApp (mkConst ``List.nil [Level.zero]) element)
  let height := getMaxHeight (← getEnv) value + 1
  let fullName := (← getCurrNamespace) ++ name.getId
  liftCoreM <| addDecl (.defnDecl {
    name := fullName, levelParams := [], type, value,
    hints := .regular height, safety := .safe })
  modifyEnv (addNoncomputable · fullName)

end Airbender.Compiler.BlockPartsImport
