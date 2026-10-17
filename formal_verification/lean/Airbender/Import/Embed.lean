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
elab "import_clean " name:ident " from " path:str metadata:(" trace_metadata")? : command => do
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
  if metadata.isSome then
    let columns ← match c.traceColumns with
      | .ok columns => pure columns
      | .error e => throwError "v2 clock metadata import failed: {e}"
    let ports ← match c.memoryPorts with
      | .ok ports => pure ports
      | .error e => throwError "v2 memory metadata import failed: {e}"
    let pair : Vector Nat 2 → CommandElabM (TSyntax `term) := fun v => `(#v[$(quote v[0]), $(quote v[1])])
    let clock : Trace.TimestampPort → CommandElabM (TSyntax `term) := fun port => do
      `((⟨$(quote port.offset), $(← pair port.previous), $(quote port.borrow)⟩ : Trace.TimestampPort))
    let clockTerms ← columns.ports.mapM clock
    let traceName := mkIdent (name.getId.appendAfter "TraceColumns")
    elabCommand (← `(def $traceName : Trace.TraceColumns :=
      ⟨$(quote columns.execute), $(← pair columns.initialPC), $(← pair columns.finalPC),
        $(← pair columns.initialTime), $(← pair columns.finalTime), #[$[$clockTerms],*]⟩))
    let portTerms ← ports.mapM fun port => do
      let address ← match port.address with
        | .register index => `(Trace.MemoryAddress.register $(quote index))
        | .mixed selector polarity indices =>
          `(Trace.MemoryAddress.mixed $(quote selector) $(quote polarity) $(← pair indices))
        | _ => throwError "unsupported v2 direct address"
      let .u16 read := port.readValue | throwError "v2 direct word must have two limbs"
      let write ← match port.writeValue with
        | none => `(none)
        | some (.u16 write) => `(some (Trace.WordColumns.u16 $(← pair write)))
        | _ => throwError "v2 direct write must have two limbs"
      `((⟨$(← clock port.clock), $address, Trace.WordColumns.u16 $(← pair read), $write⟩ : Trace.MemoryPort))
    let portsName := mkIdent (name.getId.appendAfter "MemoryPorts")
    elabCommand (← `(def $portsName : Array Trace.MemoryPort := #[$[$portTerms],*]))

end Airbender
