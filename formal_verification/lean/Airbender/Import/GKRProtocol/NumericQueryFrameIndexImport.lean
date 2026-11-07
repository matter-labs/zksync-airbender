import Airbender.Proofs.GKRProtocol.NumericQueryFrameIndexedChecks
import Lean.AddDecl
import Lean.Meta.Reduce

namespace Airbender.Compiler.NumericQueryFrameIndexImport
open Lean Elab Command
set_option warningAsError true

private def nonNumeric : Lean.Expr → Option String
  | .lit (.natVal _) => none
  | .const name _ => if [``NumericQueryFrameChecks.Index.mk,
      ``NumericPolynomialChecks.LookupTable.leaf, ``NumericPolynomialChecks.LookupTable.branch,
      ``List.cons, ``List.nil, ``Nat, ``List].contains name then none else some name.toString
  | .app fn argument => (nonNumeric fn).or (nonNumeric argument)
  | .mdata _ value => nonNumeric value
  | _ => some "non-numeric expression node"

/-- Materialize closed indexes. Separate kernel equalities bind every component. -/
elab "numeric_query_frame_index " name:ident " := " source:term : command => do
  let value ← liftTermElabM do
    let value ← Term.elabTermEnsuringType source (mkConst ``NumericQueryFrameChecks.Index)
    Term.synthesizeSyntheticMVarsNoPostponing
    Meta.reduce (← instantiateMVars value)
  if let some name := nonNumeric value then
    throwError "query frame index did not reduce to closed numeric data: {name}"
  liftCoreM <| addDecl (.defnDecl {
    name := (← getCurrNamespace) ++ name.getId
    levelParams := []
    type := mkConst ``NumericQueryFrameChecks.Index
    value
    hints := .regular 0
    safety := .safe
  })

end Airbender.Compiler.NumericQueryFrameIndexImport
