module
public meta import Lean.PrettyPrinter
public import Lean.PrettyPrinter
public meta import Proven.GKRProtocol.NumericFunctionalBaseChecks
public meta import Lean.AddDecl
public meta import Lean.Meta.Reduce
public import Proven.GKRProtocol.NumericFunctionalBaseChecks
public import Lean.AddDecl
public import Lean.Meta.Reduce

public meta section
set_option warningAsError true

namespace Airbender.Compiler.NumericFunctionalBaseImport
open Lean Elab Command

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
  let body ← liftTermElabM <| PrettyPrinter.delab value
  elabCommand (← `(@[expose] def $name : List NumericFunctionalBaseChecks.Data := $body))

end Airbender.Compiler.NumericFunctionalBaseImport
