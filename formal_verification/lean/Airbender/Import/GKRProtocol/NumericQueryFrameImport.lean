import Airbender.Proofs.GKRProtocol.NumericQueryFrameChecks
import Lean.AddDecl
import Lean.Meta.Reduce

namespace Airbender.Compiler.NumericQueryFrameImport
open Lean Elab Command
set_option warningAsError true

private def nonNumeric : Lean.Expr → Option String
  | .lit (.natVal _) => none
  | .const name _ => if [``NumericQueryFrameChecks.Capture.mk, ``List.cons, ``List.nil,
      ``Prod.mk, ``Nat, ``List, ``Prod, ``NumericPolynomialChecks.Data].contains name then none else some name.toString
  | .app fn argument => (nonNumeric fn).or (nonNumeric argument)
  | .mdata _ value => nonNumeric value
  | _ => some "non-numeric expression node"

/-- Materialize only closed natural data. A separate kernel equality binds its source. -/
elab "numeric_query_frame_capture " name:ident " := " source:term : command => do
  let value ← liftTermElabM do
    let value ← Term.elabTermEnsuringType source (mkConst ``NumericQueryFrameChecks.Capture)
    Term.synthesizeSyntheticMVarsNoPostponing
    Meta.reduce (← instantiateMVars value)
  if let some name := nonNumeric value then
    throwError "query frame capture did not reduce to closed numeric data: {name}"
  liftCoreM <| addDecl (.defnDecl {
    name := (← getCurrNamespace) ++ name.getId
    levelParams := []
    type := mkConst ``NumericQueryFrameChecks.Capture
    value
    hints := .regular 0
    safety := .safe
  })

end Airbender.Compiler.NumericQueryFrameImport
