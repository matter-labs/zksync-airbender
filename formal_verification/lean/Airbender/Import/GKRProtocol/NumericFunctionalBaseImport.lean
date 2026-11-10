import Airbender.Proofs.GKRProtocol.NumericFunctionalBaseChecks
import Lean.AddDecl
import Lean.Meta.Reduce

namespace Airbender.Compiler.NumericFunctionalBaseImport
open Lean Elab Command
set_option warningAsError true

private def nonNumeric : Lean.Expr → Option String
  | .lit (.natVal _) => none
  | .const name _ => if [``NumericFunctionalBaseChecks.Data.mk, ``NumericFunctionalBaseChecks.Data,
      ``List.cons, ``List.nil, ``Prod.mk, ``Nat, ``List, ``Prod].contains name then none else some name.toString
  | .app fn argument => (nonNumeric fn).or (nonNumeric argument)
  | .mdata _ value => nonNumeric value
  | _ => some "non-numeric expression node"

/-- Materialize only closed natural data. Separate kernel equalities bind its source. -/
elab "numeric_functional_base_capture " name:ident " := " source:term : command => do
  let value ← liftTermElabM do
    let value ← Term.elabTermEnsuringType source (mkApp (mkConst ``List [Level.zero]) (mkConst ``NumericFunctionalBaseChecks.Data))
    Term.synthesizeSyntheticMVarsNoPostponing
    Meta.reduce (← instantiateMVars value)
  if let some name := nonNumeric value then
    throwError "functional base capture did not reduce to closed numeric data: {name}"
  liftCoreM <| addDecl (.defnDecl {
    name := (← getCurrNamespace) ++ name.getId
    levelParams := []
    type := mkApp (mkConst ``List [Level.zero]) (mkConst ``NumericFunctionalBaseChecks.Data)
    value
    hints := .regular 0
    safety := .safe
  })

end Airbender.Compiler.NumericFunctionalBaseImport
