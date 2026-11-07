import Airbender.Proofs.Tables.BlockSlices
import Lean.Elab.Term

namespace Airbender.Setup.Proofs
open Lean Elab Command
set_option warningAsError true

/-- Name only the stored literal template of an imported periodic block.
    Subsequent kernel proofs check the source connection and every value. -/
elab "literal_periodic_template " name:ident " from " source:term
    " block " index:num : command => do
  let value ← liftTermElabM do
    let expression ← Lean.Elab.Term.elabTerm source (some (mkConst ``Airbender.Setup.Column))
    Lean.Meta.whnf expression
  let value := value.consumeMData
  unless value.getAppFn.isConstOf ``Airbender.Setup.Column.mk && value.getAppArgs.size == 1 do
    throwError "template source did not reduce to an imported literal Column"
  let blocks ← literalArray value.getAppArgs[0]!
  let some selected := blocks[index.getNat]? | throwError "template block is out of bounds"
  let selected := selected.consumeMData
  unless selected.getAppFn.isConstOf ``Airbender.Setup.Block.periodic &&
      selected.getAppArgs.size == 3 do
    throwError "template source is not a periodic block"
  let template := selected.getAppArgs[2]!
  let type := mkApp (mkConst ``Array [Level.zero]) (mkConst ``Nat)
  let fullName := (← getCurrNamespace) ++ name.getId
  let height := getMaxHeight (← getEnv) template + 1
  liftCoreM <| addDecl (.defnDecl {
    name := fullName, levelParams := [], type, value := template,
    hints := .regular height, safety := .safe })
  modifyEnv (addNoncomputable · fullName)

end Airbender.Setup.Proofs
