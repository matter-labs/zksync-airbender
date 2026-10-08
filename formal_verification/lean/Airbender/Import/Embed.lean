import Airbender.Import.Parse
import Airbender.Import.Coefficients
import Airbender.Review.RangeChecks
import Airbender.Review.Lookups
import Airbender.Review.ByteTables
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
elab "import_clean " name:ident " from " path:str comparisons:(" comparison_lookups")?
    muldiv:(" mul_div_lookups")? shifts:(" shift_binop_lookups")? memory:(" word_memory_lookups")?
    submemory:(" subword_memory_lookups")? unified:(" unified_reduced_lookups")?
    blake:(" blake_g_lookups")? blakeRound:(" blake_round_lookups")?
    bigint:(" bigint_lookups")? : command => do
  if (comparisons.isSome.toNat + muldiv.isSome.toNat + shifts.isSome.toNat +
      memory.isSome.toNat + submemory.isSome.toNat + unified.isSome.toNat + blake.isSome.toNat +
      blakeRound.isSome.toNat + bigint.isSome.toNat) > 1 then
    throwError "select one fixed-lookup family"
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
  let memoryFamily := memory.isSome || submemory.isSome || unified.isSome || blake.isSome ||
    blakeRound.isSome || bigint.isSome
  let tableWidth := if bigint.isSome then 3 else if blakeRound.isSome then 4 else if unified.isSome then 10 else 9
  let rom := mkIdent (if submemory.isSome || unified.isSome || blake.isSome || blakeRound.isSome ||
    bigint.isSome then `setup else `rom)
  let generic ← if memoryFamily then do
    let queries ← match (if bigint.isSome then c.bigintQueries else if blakeRound.isSome then c.blakeRoundQueries
        else if blake.isSome then c.blakeGQueries else if unified.isSome then c.unifiedReducedQueries
        else if submemory.isSome then c.subwordMemoryQueries else c.wordMemoryQueries) with
      | .ok queries => pure queries
      | .error e => throwError "circuit import failed: {e}"
    queries.toList.mapM fun entries => do
      let entries ← entries.toList.mapM cleanExprSyntax
      let entries := entries.toArray
      `(_root_.FlatOperation.lookup {
        table := ($rom).toRaw
        entry := #v[$[$entries],*]
      })
    else if comparisons.isSome || muldiv.isSome then do
    let queries ← match (if comparisons.isSome then c.comparisonQueries else c.mulDivQueries) with
      | .ok queries => pure queries
      | .error e => throwError "circuit import failed: {e}"
    queries.toList.mapM fun (id, entries) => do
      let some keyExpr := entries[0]? | throwError "comparison lookup is missing its key"
      let key ← cleanExprSyntax keyExpr
      let value ← match entries[1]? with
        | some expr => cleanExprSyntax expr
        | none => cleanConstantSyntax 0
      let query ← match id with
        | 1 => `(Airbender.Verification.pairLookup Airbender.Verification.regIsZeroTable $key $value)
        | 5 => `(Airbender.Verification.pairLookup Airbender.Verification.u16SignTable $key $value)
        | 31 => `(Airbender.Verification.pairLookup Airbender.Verification.conditionalTable $key $value)
        | 41 => `(Airbender.Verification.pairLookup Airbender.Verification.u16LowByteTable $key $value)
        | 26 => `(Airbender.Verification.range13 $key)
        | 2 => do
          let some cleaned := entries[2]? | throwError "cleanup lookup is missing its result"
          `(Airbender.Verification.jumpCleanup $key $value $(← cleanExprSyntax cleaned))
        | _ => throwError "unsupported comparison table"
      `(_root_.FlatOperation.lookup $query)
    else if shifts.isSome then do
      let queries ← match c.shiftBinopQueries with
        | .ok queries => pure queries
        | .error e => throwError "circuit import failed: {e}"
      queries.toList.mapM fun entries => do
        let entries ← entries.toList.mapM cleanExprSyntax
        let entries := entries.toArray
        `(_root_.FlatOperation.lookup (Airbender.Verification.shiftBinopLookup #v[$[$entries],*]))
    else pure []
  let ops := (ss ++ lookups ++ generic).toArray
  let prime := mkIdent `p
  if memoryFamily then
    elabCommand (← `(def $name {$prime : Nat} [Fact (Nat.Prime $prime)]
      ($rom : _root_.Table (ZMod $prime) (_root_.fields $(quote tableWidth))) :
      List (_root_.FlatOperation (ZMod $prime)) := [$[$ops],*]))
  else
    elabCommand (← `(def $name {$prime : Nat} [Fact (Nat.Prime $prime)] :
      List (_root_.FlatOperation (ZMod $prime)) := [$[$ops],*]))
  let sourceName := mkIdent (name.getId.appendAfter "SourceBytes")
  elabCommand (← `(def $sourceName : String := $(quote source)))
  let namesName := mkIdent (name.getId.appendAfter "VariableNames")
  let names ← c.variable_names.entries.toList.mapM fun (v, n) =>
    `((($(quote v) : Nat), ($(quote n) : String)))
  let names := names.toArray
  elabCommand (← `(def $namesName : List (Nat × String) := [$[$names],*]))
  if blake.isSome || blakeRound.isSome || bigint.isSome then
    let ports ← match c.indirectPorts with
      | .ok ports => pure ports
      | .error e => throwError "indirect port import failed: {e}"
    let portTerms ← ports.toList.mapM fun port => do
      let base := port.baseColumns.toArray.map quote
      let reads := port.readColumns.toArray.map quote
      let writes ← match port.writeColumns with
        | none => `(none)
        | some columns =>
          let columns := columns.toArray.map quote
          `(some #v[$[$columns],*])
      `(Airbender.Verification.IndirectPort.mk $(quote port.register) $(quote port.access)
        #v[$[$base],*] $(quote port.scale) $(quote port.offsetColumn) $(quote port.constant)
        #v[$[$reads],*] $writes)
    let portsName := mkIdent (name.getId.appendAfter "IndirectPorts")
    let portTerms := portTerms.toArray
    elabCommand (← `(def $portsName : Vector Airbender.Verification.IndirectPort $(quote ports.size) :=
      #v[$[$portTerms],*]))

end Airbender
