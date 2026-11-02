import Airbender.Proofs.GKRProtocol.NumericHelperValidityChecks
import Lean.AddDecl
import Lean.Meta.Reduce

namespace Airbender.Compiler.NumericHelperValidityImport
open Lean Elab Command
set_option warningAsError true

private def nonNumeric : Lean.Expr → Option String
  | .lit (.natVal _) => none
  | .const name _ => if [``NumericHelperValidityChecks.Capture.mk, ``NumericHelperValidityChecks.Capture,
      ``NumericHelperValidityChecks.Borrow.mk, ``NumericHelperValidityChecks.Borrow,
      ``NumericHelperValidityChecks.Transport.mk, ``NumericHelperValidityChecks.Transport,
      ``NumericPolynomialChecks.Data, ``List.cons, ``List.nil, ``Prod.mk, ``Nat, ``List, ``Prod].contains name then none else some name.toString
  | .app fn argument => (nonNumeric fn).or (nonNumeric argument)
  | .mdata _ value => nonNumeric value
  | _ => some "non-numeric expression node"

elab "numeric_helper_validity_capture " name:ident " := " source:term : command => do
  let value ← liftTermElabM do
    let value ← Term.elabTermEnsuringType source (mkConst ``NumericHelperValidityChecks.Capture)
    Term.synthesizeSyntheticMVarsNoPostponing
    Meta.reduce (← instantiateMVars value)
  if let some name := nonNumeric value then
    throwError "helper validity capture did not reduce to closed numeric data: {name}"
  liftCoreM <| addDecl (.defnDecl {
    name := (← getCurrNamespace) ++ name.getId
    levelParams := []
    type := mkConst ``NumericHelperValidityChecks.Capture
    value
    hints := .regular 0
    safety := .safe
  })

end Airbender.Compiler.NumericHelperValidityImport
