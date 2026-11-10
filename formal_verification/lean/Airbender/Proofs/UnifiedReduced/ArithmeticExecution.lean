import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Review.Helpers.Core.SerializedInverse
import Airbender.Review.Trace.UnifiedReduced.Execution
import Airbender.Proofs.UnifiedReduced.TraceSoundness
import Airbender.Proofs.UnifiedReduced.RegisterRetirement

namespace Airbender.UnifiedReduced.Proofs
open Arithmetic Reference.RiscV Reference.RiscV.Sail Reference.Sail Trace Trace.Proofs
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

theorem arithmetic_clause [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception] (input : Input) :
    instructionClause (arithmeticInstruction input) = some (Sail.execution input) := by
  cases op : input.row.opcode <;> simp [arithmeticInstruction, instructionClause, Reference.RiscV.Sail.registerClause, Sail.execution, Sail.instruction, Option.get_some, op]

theorem arithmetic_register_retirement [Fact p.Prime]
    (hp : FieldCapacity.NoWrap p 524288) {setup : Table (ZMod p) (fields 10)}
    {cells : List Cell} {w : Nat → ZMod p} {entry : ProgramEntry} {input : Input}
    (core : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (fields : decoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query) (encoding : entry.instruction = arithmeticInstruction input)
    (epoch : Nat) {before after : State}
    (history : SailHistory cells (rowEvents epoch (⟨.machine, w⟩ : Row p UnifiedFamily)).reverse before after)
    (spec : stepSpec (retiredState before (Control.initialPC w).toBitVec) (Sail.execution input) input.rd
      ⟨Control.destination w, Control.finalPC w⟩) :
    run (normalStep (Sail.execution input)) (retiredState before (Control.initialPC w).toBitVec) =
        .ok SailRV32.Functions.RETIRE_SUCCESS (retiredState after (Control.finalPC w).toBitVec) := by
  have metadata : entry.data.mask < 262144 ∧ entry.data.rd = match input.rd with | .Regidx bits => bits := by
    rw [encoding] at fields
    rcases input with ⟨⟨op, left, right, immediate, pc⟩, ⟨rs1⟩, ⟨rs2⟩, ⟨rd⟩, imm, upper, state⟩
    change BitVec 5 at rs1 rs2 rd
    cases op <;> by_cases zero : rd = (0#5)
    all_goals simp [arithmeticInstruction, Sail.instruction, decoderFields, Trace.decoderFields, arithmeticFields,
      Trace.arithmeticFields, DecoderData.mapFamily, zero] at fields
    all_goals rw [← fields]
    all_goals simp [zero]
  exact register_retirement hp core fields query metadata.1 metadata.2 epoch history spec

theorem arithmetic_retirement [Fact p.Prime] [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    (hp : FieldCapacity.NoWrap p 524288) {setup : Table (ZMod p) (fields 10)}
    {cells : List Cell} {w : Nat → ZMod p} {entry : ProgramEntry} {input : Input}
    (core : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (fields : decoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query) (encoding : entry.instruction = arithmeticInstruction input)
    (epoch : Nat) {before after : State}
    (history : SailHistory cells (rowEvents epoch (⟨.machine, w⟩ : Row p UnifiedFamily)).reverse before after)
    (spec : stepSpec (retiredState before (Control.initialPC w).toBitVec) (Sail.execution input) input.rd
      ⟨Control.destination w, Control.finalPC w⟩) :
    ∃ clause, instructionClause entry.instruction = some clause ∧
      run (normalStep clause) (retiredState before (Control.initialPC w).toBitVec) =
        .ok SailRV32.Functions.RETIRE_SUCCESS (retiredState after (Control.finalPC w).toBitVec) := by
  refine ⟨Sail.execution input, ?_, arithmetic_register_retirement hp core fields query encoding epoch history spec⟩
  rw [encoding]
  exact arithmetic_clause input

theorem arithmetic_execution_from_memory [Fact p.Prime] [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    (hp : FieldCapacity.NativeRomCapacity p) (inverse : SerializedInverse.Clock p)
    {trace : UnifiedTrace p} {initial : State} {cells : List Cell} {program : List ProgramEntry}
    {projection : SailRV32.instruction → Option (DecoderData UnifiedFamily)}
    (accepted : Accepted trace)
    (inputs : NativeInputs projection trace initial cells program)
    (registers : ∀ index, Cell.register index ∈ cells)
    {w : Nat → ZMod p} (member : (⟨.machine, w⟩ : Row p UnifiedFamily) ∈ trace.rows)
    {before after : State} {input : Input} {entry : ProgramEntry}
    (words : WordMapping input ⟨Control.destination w, Control.finalPC w⟩ w)
    (atRow : input.before = retiredState before (Control.initialPC w).toBitVec)
    (position : RowPosition trace initial cells ⟨.machine, w⟩ input.before)
    (fields : decoderFields entry.instruction = some entry.data)
    (memory : MemoryExecution trace initial cells) (query : decoderQuery w = entry.query)
    (encoding : entry.instruction = arithmeticInstruction input)
    (history : SailHistory cells (rowEvents trace.memoryEpoch (⟨.machine, w⟩ : Row p UnifiedFamily)).reverse before after) :
    ∃ clause, instructionClause entry.instruction = some clause ∧
      run (normalStep clause) (retiredState before (Control.initialPC w).toBitVec) =
        .ok SailRV32.Functions.RETIRE_SUCCESS (retiredState after (Control.finalPC w).toBitVec) := by
  have clockSize : 2 * timestampBase + 4 < p := by dsimp [timestampBase]; omega
  have result := arithmetic_soundness_from_memory clockSize inverse inputs accepted memory member
    (fun index _ => registers index) words position fields query encoding
  have core := Verification.holds_of_sublist (accepted.constraints _ member)
    (List.sublist_append_left (importedConstraints trace.rom) importedConstraintsTimestampLookups)
  change FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints trace.rom) at core
  have spec : stepSpec (retiredState before (Control.initialPC w).toBitVec) (Sail.execution input) input.rd
      ⟨Control.destination w, Control.finalPC w⟩ := by
    change stepSpec input.before (Sail.execution input) input.rd _ at result
    rw [atRow] at result
    exact result
  exact arithmetic_retirement (by omega) core fields query encoding trace.memoryEpoch history spec

theorem arithmetic_execution [Fact p.Prime] [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    (hp : FieldCapacity.NativeRomCapacity p) (inverse : SerializedInverse.Clock p)
    {trace : UnifiedTrace p} {initial : State} {cells : List Cell} {program : List ProgramEntry}
    (accepted : Accepted trace) (decoded : Decoded trace program)
    (inputs : NativeInputs decoderFields trace initial cells program)
    (registers : ∀ index, Cell.register index ∈ cells)
    {w : Nat → ZMod p} (member : (⟨.machine, w⟩ : Row p UnifiedFamily) ∈ trace.rows)
    {before after : State} {input : Input} {entry : ProgramEntry}
    (words : WordMapping input ⟨Control.destination w, Control.finalPC w⟩ w)
    (atRow : input.before = retiredState before (Control.initialPC w).toBitVec)
    (position : RowPosition trace initial cells ⟨.machine, w⟩ input.before)
    (present : entry ∈ program) (query : decoderQuery w = entry.query)
    (encoding : entry.instruction = arithmeticInstruction input)
    (history : SailHistory cells (rowEvents trace.memoryEpoch (⟨.machine, w⟩ : Row p UnifiedFamily)).reverse before after) :
    ∃ clause, instructionClause entry.instruction = some clause ∧
      run (normalStep clause) (retiredState before (Control.initialPC w).toBitVec) =
        .ok SailRV32.Functions.RETIRE_SUCCESS (retiredState after (Control.finalPC w).toBitVec) := by
  obtain ⟨addresses, image⟩ := inputs.programImage
  exact arithmetic_execution_from_memory hp inverse accepted inputs registers member words atRow position
    (run_program_sources image entry present).fields
    (memory_execution (by dsimp [timestampBase]; omega) inverse accepted inputs decoded) query encoding history

end Airbender.UnifiedReduced.Proofs
