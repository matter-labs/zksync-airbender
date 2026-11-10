import Airbender.Proofs.GKRProtocol.NumericMemoryFrameChecks
import Lean.AddDecl
import Lean.Meta.Reduce

namespace Airbender.Compiler.NumericMemoryFrameImport
open Lean Elab Command
set_option warningAsError true

private def nonNumeric : Lean.Expr → Option String
  | .lit (.natVal _) => none
  | .const name _ => if [``NumericMemoryFrameChecks.Capture.mk,
      ``NumericPolynomialChecks.LookupTable.leaf, ``NumericPolynomialChecks.LookupTable.branch,
      ``List.cons, ``List.nil, ``Prod.mk, ``Nat, ``List, ``Prod,
      ``NumericPolynomialChecks.Data].contains name then none else some name.toString
  | .app fn argument => (nonNumeric fn).or (nonNumeric argument)
  | .mdata _ value => nonNumeric value
  | _ => some "non-numeric expression node"

/-- Materialize only closed natural data. Separate kernel equalities bind its source. -/
elab "numeric_memory_frame_capture " name:ident " := " source:term : command => do
  let value ← liftTermElabM do
    let value ← Term.elabTermEnsuringType source (mkConst ``NumericMemoryFrameChecks.Capture)
    Term.synthesizeSyntheticMVarsNoPostponing
    Meta.reduce (← instantiateMVars value)
  if let some name := nonNumeric value then
    throwError "memory frame capture did not reduce to closed numeric data: {name}"
  liftCoreM <| addDecl (.defnDecl {
    name := (← getCurrNamespace) ++ name.getId
    levelParams := []
    type := mkConst ``NumericMemoryFrameChecks.Capture
    value
    hints := .regular 0
    safety := .safe
  })

end Airbender.Compiler.NumericMemoryFrameImport
