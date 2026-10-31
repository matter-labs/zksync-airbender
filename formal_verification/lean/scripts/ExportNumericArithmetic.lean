import Airbender.Proofs.GKRProtocol.NumericArithmeticChecks
import Lean

namespace NumericArithmeticExport
open Lean Elab Command

/-- The tool emits untrusted data. Each capture checks its bindings in the kernel. -/
private partial def listValues (value : Expr) : CommandElabM (Array Expr) := do
  let value ← liftTermElabM <| Meta.whnf value
  if value.getAppFn.isConstOf ``List.nil then return #[]
  unless value.getAppFn.isConstOf ``List.cons do throwError "expected a closed list"
  let args := value.getAppArgs
  return #[args[1]!] ++ (← listValues args[2]!)

private def natural (value : Expr) : CommandElabM Nat := do
  match ← liftTermElabM <| Meta.reduce value with
  | .lit (.natVal number) => return number
  | _ => throwError "expected a closed natural"

private def polynomial (value : Expr) : CommandElabM Json := do
  let terms ← (← listValues value).mapM fun term => do
    let term ← liftTermElabM <| Meta.whnf term
    unless term.getAppFn.isConstOf ``Prod.mk do throwError "expected a polynomial term"
    let args := term.getAppArgs
    let scalar ← natural (← liftTermElabM <| Meta.mkAppM ``ZMod.val #[args[2]!])
    let wires ← (← listValues args[3]!).mapM fun wire => do
      natural (← liftTermElabM <| Meta.mkAppM ``Fin.val #[wire])
    return Json.arr #[toJson scalar, toJson wires]
  return Json.arr terms

private def originalTerm (term : TSyntax `term) : CommandElabM Expr := liftTermElabM do
  let value ← Term.elabTerm term none
  Term.synthesizeSyntheticMVarsNoPostponing
  instantiateMVars value

private def combinations (value : Expr) : CommandElabM Json := do
  let rows ← (← listValues value).mapM fun row => do
    let terms ← (← listValues row).mapM fun term => do
      let term ← liftTermElabM <| Meta.whnf term
      unless term.getAppFn.isConstOf ``Prod.mk do throwError "expected a certificate term"
      let args := term.getAppArgs
      let payload ← polynomial args[2]!
      let index ← natural (← liftTermElabM <| Meta.mkAppM ``Fin.val #[args[3]!])
      return Json.arr #[payload, toJson index]
    return Json.arr terms
  return Json.arr rows

syntax "export_numeric_arithmetic " ident " to " str : command
elab_rules : command
  | `(export_numeric_arithmetic $scope:ident to $destination:str) => do
    let artifact := mkIdent (scope.getId ++ `artifact)
    let extensionData := mkIdent (scope.getId ++ `extensionData)
    let backwardData := mkIdent (scope.getId ++ `backwardData)
    let forwardData := mkIdent (scope.getId ++ `forwardData)
    let addresses := mkIdent (scope.getId ++ `addresses)
    let fields ← #[
      ("source", ← `(($artifact).source)),
      ("lowered", ← `(($artifact).translation.lowered)),
      ("extension", ← `(($extensionData).toList)),
      ("gateInput", ← `(($artifact).gates.map Airbender.Compiler.NumericArithmeticChecks.gateInput)),
      ("gateOutput", ← `(($artifact).gates.map Airbender.Compiler.NumericArithmeticChecks.gateOutput))].mapM fun (name, term) => do
        let rows ← (← listValues (← originalTerm term)).mapM polynomial
        return (name, Json.arr rows)
    let backward ← combinations (← originalTerm (← `(($backwardData).toList)))
    let forward ← combinations (← originalTerm (← `(($forwardData).toList)))
    let keys ← (← listValues (← originalTerm
      (← `(($addresses).map Airbender.Compiler.AddressUniqueChecks.addressCode)))).mapM natural
    let payload := Json.mkObj (fields.toList ++ [("backward", backward), ("forward", forward), ("keys", toJson keys)])
    IO.FS.writeFile destination.getString (payload.compress ++ "\n")
end NumericArithmeticExport
