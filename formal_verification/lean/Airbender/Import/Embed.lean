import Airbender.Import.Parse
import Airbender.Import.Coefficients
import Airbender.Review.Helpers.Tables.WordROM
import Airbender.Review.Circuits.JumpBranchSlt.Tables.Control
import Airbender.Review.Helpers.Tables.SmallRange
import Airbender.Review.Circuits.ShiftBinop.Tables.Native
import Airbender.Review.Circuits.SubwordMemory.Tables.Native
import Airbender.Review.Helpers.Tables.SubwordOffset
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

/-- Import v2 compiled row equations, ranges and selected fixed queries into Clean.
    Import/generation fidelity and setup/memory arguments remain explicit boundaries. -/
elab "import_clean " name:ident " from " path:str fixed:(" word_memory_lookups")? control:(" control_lookups")? muldiv:(" mul_div_lookups")? shift:(" shift_binop_lookups")? subword:(" subword_memory_lookups")? metadata:(" trace_metadata")? : command => do
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
  let prime := mkIdent `p
  let rom := mkIdent `rom
  if fixed.isSome.toNat + control.isSome.toNat + muldiv.isSome.toNat + shift.isSome.toNat + subword.isSome.toNat > 1 then throwError "choose one native fixed-table profile"
  unless c.witness_layout.width_3_lookups.isEmpty || fixed.isSome || control.isSome || muldiv.isSome || shift.isSome || subword.isSome do
    throwError "v2 fixed lookups require an explicit native target"
  if (fixed.isSome || control.isSome || muldiv.isSome || shift.isSome || subword.isSome) && c.witness_layout.width_3_lookups.isEmpty then
    throwError "v2 fixed-table target has no native fixed lookups"
  for query in c.witness_layout.width_3_lookups do
    let allowed := match query.table_index with
      | .Variable _ => (shift.isSome && c.hasShiftLookups) || (subword.isSome && c.hasSubwordLookups)
      | .Constant id => match id with
        | .RomAddressSpaceSeparator => fixed.isSome || subword.isSome
        | .RomRead => fixed.isSome
        | .MemoryGetOffsetAndMaskWithTrap => subword.isSome
        | .ConditionalJmpBranchSlt | .JumpCleanupOffset => control.isSome
        | .RangeCheckSmall => muldiv.isSome
    unless allowed do throwError "native fixed tables do not match the explicit target"
  let fixedLookups ← c.witness_layout.width_3_lookups.toList.mapM fun query => do
    let entries ← match query.input_columns.mapM c.lookupExpression with
      | .ok entries => entries.mapM cleanExprSyntax
      | .error e => throwError "v2 fixed lookup import failed: {e}"
    if let .Variable address := query.table_index then
      let selector ← match c.logicalVariable address with
        | .ok index => cleanExprSyntax (.Var index)
        | .error error => throwError "v2 dynamic selector import failed: {error}"
      if subword.isSome then
        return ← `(_root_.FlatOperation.lookup (Verification.NativeSubwordLookup.lookup $rom
          #v[$(entries[0]!), $(entries[1]!), $(entries[2]!)] $selector))
      return ← `(_root_.FlatOperation.lookup (Verification.NativeShiftLookup.lookup
        #v[$(entries[0]!), $(entries[1]!), $(entries[2]!)] $selector))
    let table ← match query.table_index with
      | .Constant .RomAddressSpaceSeparator => `(Verification.romSeparatorTable (p := $prime))
      | .Constant .RomRead => `(Verification.romWordTable (p := $prime) $rom)
      | .Constant .MemoryGetOffsetAndMaskWithTrap => `(Verification.SubwordOffset.table (p := $prime))
      | .Constant .ConditionalJmpBranchSlt => `(Verification.conditionalControlTable (p := $prime))
      | .Constant .JumpCleanupOffset => `(Verification.jumpCleanupTable (p := $prime))
      | .Constant .RangeCheckSmall => `(Verification.smallRangeTable (p := $prime))
      | .Variable _ => throwError "unexpected dynamic lookup profile"
    `(_root_.FlatOperation.lookup (Verification.fixed3 $table
      #v[$(entries[0]!), $(entries[1]!), $(entries[2]!)]))
  let ops := (assertions ++ lookups ++ timestamps ++ fixedLookups).toArray
  if fixed.isSome || subword.isSome then
    elabCommand (← `(def $name {$prime : Nat} [Fact (Nat.Prime $prime)]
      ($rom : Verification.WordROM) : List (_root_.FlatOperation (ZMod $prime)) := [$[$ops],*]))
  else
    elabCommand (← `(def $name {$prime : Nat} [Fact (Nat.Prime $prime)] :
      List (_root_.FlatOperation (ZMod $prime)) := [$[$ops],*]))
  if metadata.isSome then
    let setup ← match c.setupColumns with
      | .ok setup => pure setup
      | .error e => throwError "v2 setup metadata import failed: {e}"
    let setupName := mkIdent (name.getId.appendAfter "SetupColumns")
    elabCommand (← `(def $setupName : Verification.SetupColumns :=
      ⟨$(quote setup.traceLength), $(quote setup.width), $(quote setup.range16),
        $(quote setup.timestamp19), $(quote setup.genericStart), $(quote setup.genericGroups),
        $(quote setup.decoderStart), $(quote setup.decoderCapacity), $(quote setup.genericRows)⟩))
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
    let decoder ← match c.decoderColumns with
      | .ok decoder => pure decoder
      | .error e => throwError "v2 decoder metadata import failed: {e}"
    let decoderName := mkIdent (name.getId.appendAfter "DecoderColumns")
    elabCommand (← `(def $decoderName : Trace.DecoderColumns :=
      ⟨$(quote decoder.rs1), $(quote decoder.rs2), $(quote decoder.rd),
        $(quote decoder.rdIsZero), $(← pair decoder.immediate),
        $(quote decoder.funct3), $(quote decoder.mask)⟩))

end Airbender
