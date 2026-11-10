import Airbender.Proofs.GKRProtocol.CleanIdealChecks
import Lean

namespace CleanIdealExport
open Lean Elab Command

/-- Export untrusted numeric data. Source bindings remain kernel obligations. -/
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

private def witness (value : Expr) : CommandElabM Json := do
  let terms ← (← listValues value).mapM fun term => do
    let term ← liftTermElabM <| Meta.whnf term
    unless term.getAppFn.isConstOf ``Prod.mk do throwError "expected a certificate term"
    let args := term.getAppArgs
    let payload ← polynomial args[2]!
    let index ← natural (← liftTermElabM <| Meta.mkAppM ``Fin.val #[args[3]!])
    return Json.arr #[payload, toJson index]
  return Json.arr terms

private partial def code (value : Expr) : CommandElabM Json := do
  let value ← liftTermElabM <| Meta.whnf value
  let args := value.getAppArgs
  if value.getAppFn.isConstOf ``Airbender.Compiler.NumericExpressionChecks.Code.constant then
    return Json.arr #[toJson (0 : Nat), toJson (← natural args[0]!)]
  else if value.getAppFn.isConstOf ``Airbender.Compiler.NumericExpressionChecks.Code.atom then
    return Json.arr #[toJson (1 : Nat), toJson (← natural args[0]!)]
  else if value.getAppFn.isConstOf ``Airbender.Compiler.NumericExpressionChecks.Code.add then
    return Json.arr #[toJson (2 : Nat), ← code args[0]!, ← code args[1]!]
  else if value.getAppFn.isConstOf ``Airbender.Compiler.NumericExpressionChecks.Code.mul then
    return Json.arr #[toJson (3 : Nat), ← code args[0]!, ← code args[1]!]
  else throwError "expected an erased Clean expression"

syntax "export_clean_ideals " ident " count " num " to " str : command
elab_rules : command
  | `(export_clean_ideals $scope:ident count $countNumber:num to $destination:str) => do
    let placement := mkIdent (scope.getId ++ `placement)
    let relations := mkIdent (scope.getId ++ `relations)
    let keys := mkIdent (scope.getId ++ `placementKeys)
    let rows ← (← listValues (← originalTerm (← `($relations)))).mapM polynomial
    let mut expressions := #[]
    let mut witnesses := #[]
    let mut inputs := #[]
    for index in [:countNumber.getNat] do
      let expression := mkIdent (scope.getId ++ Name.mkSimple s!"expression{index}")
      let certificate := mkIdent (scope.getId ++ Name.mkSimple s!"witness{index}")
      expressions := expressions.push (← code (← originalTerm
        (← `(Airbender.Compiler.CleanIdealChecks.encode $placement $expression))))
      witnesses := witnesses.push (← witness (← originalTerm (← `($certificate))))
      inputs := inputs.push (← (← listValues (← originalTerm
        (← `(Airbender.Compiler.CleanExpression.inputs $expression)))).mapM natural)
    let limit ← natural (← originalTerm (← `(($keys).length)))
    let payload := Json.mkObj [("relations", Json.arr rows), ("expressions", Json.arr expressions),
      ("witnesses", Json.arr witnesses), ("inputs", toJson inputs), ("scopeLimit", toJson limit)]
    IO.FS.writeFile destination.getString (payload.compress ++ "\n")

end CleanIdealExport
