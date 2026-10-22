import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Review.Helpers.Core.SerializedInverse
import Airbender.Proofs.UnifiedReduced.ObservationMapping
import Airbender.Proofs.UnifiedReduced.ArithmeticIndex
import Airbender.Proofs.UnifiedReduced.ControlExecution
import Airbender.Proofs.UnifiedReduced.BinaryExecution
import Airbender.Proofs.UnifiedReduced.MemoryExecution
import Airbender.Review.Trace.UnifiedReduced.Execution

namespace Airbender.UnifiedReduced.Proofs
open Arithmetic Reference.RiscV Reference.RiscV.Sail Reference.Sail Trace Trace.Proofs
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

theorem row_clause_from_memory [Fact p.Prime] [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    (hp : FieldCapacity.NativeRomCapacity p) (inverse : SerializedInverse.Clock p)
    (byteInverse : SerializedInverse.Scale256 p)
    {trace : UnifiedTrace p} {initial : State} {cells : List Cell} {program : List ProgramEntry}
    {projection : SailRV32.instruction → Option (DecoderData UnifiedFamily)}
    (accepted : Accepted trace)
    (inputs : ExecutionInputsWith projection trace initial cells program)
    (memory : MemoryExecution (ROMView.data initial trace) initial cells)
    {w : Nat → ZMod p} (member : (⟨.machine, w⟩ : Row p UnifiedFamily) ∈ (ROMView.data initial trace).rows)
    {before after : State}
    (position : RowPosition (ROMView.data initial trace) initial cells ⟨.machine, w⟩
      (retiredState before (Control.initialPC w).toBitVec))
    {entry : ProgramEntry} (present : entry ∈ program)
    (source : entry.SourceWith initial decoderFields) (query : decoderQuery w = entry.query)
    (history : SailHistory cells (rowEvents trace.memoryEpoch (⟨.machine, w⟩ : Row p UnifiedFamily)).reverse before after) :
    ∃ clause, instructionClause entry.instruction = some clause ∧
      run (normalStep clause) (retiredState before (Control.initialPC w).toBitVec) =
        .ok SailRV32.Functions.RETIRE_SUCCESS (retiredState after (Control.finalPC w).toBitVec) := by
  have physicalHistory : SailHistory cells
      (rowEvents (ROMView.data initial trace).memoryEpoch (⟨.machine, w⟩ : Row p UnifiedFamily)).reverse
      before after := by
    simpa only [Data.memoryEpoch, ROMView.data, List.map_map, Function.comp_def, Trace.ROMView.token_address] using history
  have physical := ROMView.accepted (by omega) initial accepted
  have nativeInputs := ROMView.boot_inputs (by omega) inputs.boot
  have fields := source.fields
  obtain ⟨observation, observed⟩ := observe_supported w (retiredState before (Control.initialPC w).toBitVec) fields
  cases observation with
  | arithmetic input =>
    obtain ⟨encoding, state, words⟩ := observe_arithmetic observed
    exact arithmetic_execution_from_memory hp inverse physical nativeInputs inputs.registers member
      (words (arithmetic_index fields encoding query)) state (state.symm ▸ position)
      fields memory query encoding physicalHistory
  | branch input =>
    obtain ⟨encoding, state, words⟩ := observe_branch observed
    exact branch_execution_from_memory hp inverse physical nativeInputs inputs.boot.setup inputs.configuration.isa member
      words state (state.symm ▸ position) source (inputs.code entry present).2 memory query encoding physicalHistory
  | comparison input =>
    obtain ⟨encoding, state, words⟩ := observe_comparison observed
    exact comparison_execution_from_memory hp inverse physical nativeInputs inputs.boot.setup member
      words state (state.symm ▸ position) source (inputs.code entry present).2 memory query encoding physicalHistory
  | jump input =>
    obtain ⟨encoding, state, words⟩ := observe_jump observed
    exact jump_execution_from_memory hp inverse physical member
      nativeInputs inputs.boot.setup inputs.configuration.isa (by
          intro indirect
          refine ⟨inputs.configuration.privilege, inputs.landingPadDisabled ?_⟩
          cases kind : input.instruction with
          | jal imm => simp [JumpBranchSlt.Jump.Instruction.indirect, kind] at indirect
          | jalr imm => exact ⟨entry, present, imm, input.rs1, input.rd, by simpa [Jump.instruction, JumpBranchSlt.Jump.instruction, kind] using encoding⟩)
      words state (state.symm ▸ position) source (inputs.code entry present).2 memory query encoding physicalHistory
  | binary shift input =>
    obtain ⟨encoding, state, words⟩ := observe_binary observed
    exact binary_execution_from_memory hp inverse byteInverse shift physical member
      nativeInputs inputs.boot.setup words state (state.symm ▸ position) source memory query encoding physicalHistory
  | memory input =>
    obtain ⟨encoding, state, words⟩ := observe_memory observed
    have destination : input.store = false → input.rd ≠ zeroRegister := by
      intro load zero
      cases source : input.rs1 with
      | Regidx index =>
        apply inputs.loads entry present input.encodedImmediate index
        simpa only [load, Bool.false_eq_true, if_false, zero, source, zeroRegister] using encoding
    exact word_execution_from_memory hp inverse accepted member
      inputs.boot inputs.configuration inputs.ordinary destination words state (state.symm ▸ position)
      source memory query encoding history

theorem row_clause [Fact p.Prime] [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    (hp : FieldCapacity.NativeRomCapacity p) (inverse : SerializedInverse.Clock p)
    (byteInverse : SerializedInverse.Scale256 p)
    {trace : UnifiedTrace p} {initial : State} {cells : List Cell} {program : List ProgramEntry}
    (accepted : Accepted trace) (decoded : Decoded trace program)
    (inputs : ExecutionInputs trace initial cells program)
    {w : Nat → ZMod p} (member : (⟨.machine, w⟩ : Row p UnifiedFamily) ∈ (ROMView.data initial trace).rows)
    {before after : State}
    (position : RowPosition (ROMView.data initial trace) initial cells ⟨.machine, w⟩
      (retiredState before (Control.initialPC w).toBitVec))
    {entry : ProgramEntry} (present : entry ∈ program) (query : decoderQuery w = entry.query)
    (history : SailHistory cells (rowEvents trace.memoryEpoch (⟨.machine, w⟩ : Row p UnifiedFamily)).reverse before after) :
    ∃ clause, instructionClause entry.instruction = some clause ∧
      run (normalStep clause) (retiredState before (Control.initialPC w).toBitVec) =
        .ok SailRV32.Functions.RETIRE_SUCCESS (retiredState after (Control.finalPC w).toBitVec) := by
  obtain ⟨addresses, image⟩ := inputs.boot.programImage
  exact row_clause_from_memory hp inverse byteInverse accepted inputs
    (ROMView.memory_execution (by dsimp [timestampBase]; omega) inverse accepted inputs.boot decoded)
    member position present (run_program_sources image entry present) query history

end Airbender.UnifiedReduced.Proofs
