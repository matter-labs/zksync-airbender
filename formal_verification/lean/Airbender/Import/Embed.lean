import Airbender.Import.Parse
import Airbender.Import.Coefficients
import Airbender.Review.RangeChecks
import Lean

open Lean Elab Command

namespace Airbender

private def cleanConstantSyntax (n : Int) : CommandElabM (TSyntax `term) := do
  let value ← if n ≥ 0 then `(Int.ofNat $(quote n.toNat))
    else `(Int.negSucc $(quote (-n - 1).toNat))
  `(_root_.Expression.const (Int.cast $value))

/-- Emit native Clean expressions directly from decoded JSON data. -/
private partial def cleanExprSyntax (e : Airbender.Expr) : CommandElabM (TSyntax `term) := do
  match e with
  | .Constant c => cleanConstantSyntax (Artifact.signedCoefficient c)
  | .Var v => `(_root_.Expression.var ⟨$(quote v)⟩)
  | .Sum es =>
    es.foldlM (fun acc e => do `(_root_.Expression.add $acc $(← cleanExprSyntax e)))
      (← cleanConstantSyntax 0)
  | .Product es =>
    es.foldlM (fun acc e => do `(_root_.Expression.mul $acc $(← cleanExprSyntax e)))
      (← cleanConstantSyntax 1)

private def cleanStatementSyntax (s : StructuredStatement) : CommandElabM (TSyntax `term) := do
  match s with
  | .AssertZero e _ _ => `(_root_.FlatOperation.assert $(← cleanExprSyntax e))
  | .Define v _ e _ =>
    let rhs ← cleanExprSyntax e
    let negOne ← cleanConstantSyntax (-1)
    `(_root_.FlatOperation.assert
      (_root_.Expression.add (_root_.Expression.var ⟨$(quote v)⟩)
        (_root_.Expression.mul $negOne $rhs)))

/-- Emit retained equations and 16-bit range queries as native Clean operations.
    Parsing/emission remains an artifact-binding trust boundary. -/
elab "import_clean " name:ident " from " path:str : command => do
  let source ← IO.FS.readFile path.getString
  let c ← match parseCircuit source with
    | .ok c => pure c
    | .error e => throwError "circuit import failed: {e}"
  let ss ← c.structured_statements.toList.mapM cleanStatementSyntax
  let ranges ← match c.range16Expressions with
    | .ok ranges => pure ranges
    | .error e => throwError "circuit import failed: {e}"
  let lookups ← ranges.toList.mapM fun e => do
    `(_root_.FlatOperation.lookup (Airbender.Verification.range16 $(← cleanExprSyntax e)))
  let ops := (ss ++ lookups).toArray
  let prime := mkIdent `p
  elabCommand (← `(def $name {$prime : Nat} [Fact (Nat.Prime $prime)] :
    List (_root_.FlatOperation (ZMod $prime)) := [$[$ops],*]))
  let sourceName := mkIdent (name.getId.appendAfter "SourceBytes")
  elabCommand (← `(def $sourceName : String := $(quote source)))
  let namesName := mkIdent (name.getId.appendAfter "VariableNames")
  let names ← c.variable_names.entries.toList.mapM fun (v, n) =>
    `((($(quote v) : Nat), ($(quote n) : String)))
  let names := names.toArray
  elabCommand (← `(def $namesName : List (Nat × String) := [$[$names],*]))

end Airbender
