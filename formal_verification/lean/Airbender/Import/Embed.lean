import Airbender.Import.Parse
import Airbender.Import.Coefficients
import Airbender.Review.Helpers.Tables.Range
import Lean

open Lean Elab Command

namespace Airbender

private def cleanConstantSyntax (n : Int) : CommandElabM (TSyntax `term) := do
  let value ← if n ≥ 0 then `(Int.ofNat $(quote n.toNat))
    else `(Int.negSucc $(quote (-n - 1).toNat))
  `(_root_.Expression.const (Int.cast $value))

private partial def cleanExprSyntax (e : Expr) : CommandElabM (TSyntax `term) := do
  match e with
  | .Constant c => cleanConstantSyntax (Artifact.signedCoefficient c)
  | .Var v => `(_root_.Expression.var ⟨$(quote v)⟩)
  | .Sum es =>
    es.foldlM (fun acc e => do `(_root_.Expression.add $acc $(← cleanExprSyntax e)))
      (← cleanConstantSyntax 0)
  | .Product es =>
    es.foldlM (fun acc e => do `(_root_.Expression.mul $acc $(← cleanExprSyntax e)))
      (← cleanConstantSyntax 1)

/-- Import v2 compiled row equations and scalar ranges into native Clean operations.
    Import/generation fidelity and setup/memory arguments remain explicit boundaries. -/
elab "import_clean " name:ident " from " path:str : command => do
  let c ← match parseCircuit (← IO.FS.readFile path.getString) with
    | .ok c => pure c
    | .error e => throwError "v2 circuit import failed: {e}"
  let expressions ← match do
    let qs ← c.degree_2_constraints.mapM c.quadraticExpression
    let ls ← c.degree_1_constraints.mapM c.linearExpression
    pure (qs ++ ls) with
    | .ok es => pure es
    | .error e => throwError "v2 equation import failed: {e}"
  let assertions ← expressions.toList.mapM fun e => do
    `(_root_.FlatOperation.assert $(← cleanExprSyntax e))
  let ranges ← match c.witness_layout.range_check_16_lookup_expressions.mapM c.lookupExpression with
    | .ok es => pure es
    | .error e => throwError "v2 range import failed: {e}"
  let lookups ← ranges.toList.mapM fun e => do
    `(_root_.FlatOperation.lookup (Airbender.Verification.range16 $(← cleanExprSyntax e)))
  let clocks ← match c.witness_layout.timestamp_range_check_lookup_expressions.mapM c.lookupExpression with
    | .ok es => pure es
    | .error e => throwError "v2 timestamp import failed: {e}"
  let timestamps ← clocks.toList.mapM fun e => do
    `(_root_.FlatOperation.lookup (Airbender.Verification.timestamp19 $(← cleanExprSyntax e)))
  let ops := (assertions ++ lookups ++ timestamps).toArray
  let prime := mkIdent `p
  elabCommand (← `(def $name {$prime : Nat} [Fact (Nat.Prime $prime)] :
    List (_root_.FlatOperation (ZMod $prime)) := [$[$ops],*]))

end Airbender
