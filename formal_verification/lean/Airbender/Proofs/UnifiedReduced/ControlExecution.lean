import Airbender.Proofs.UnifiedReduced.RegisterRetirement
import Airbender.Proofs.UnifiedReduced.BranchSoundness
import Airbender.Proofs.UnifiedReduced.ComparisonSoundness
import Airbender.Proofs.UnifiedReduced.JumpSoundness

namespace Airbender.UnifiedReduced.Proofs
open Arithmetic Reference.RiscV Reference.RiscV.Sail Reference.Sail Trace Trace.Proofs
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

theorem branch_execution_from_memory [Fact p.Prime] [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    (hp : 4194304 ≤ p) (inverse : (-3840 : ZMod p) * 524288 = 1)
    {trace : UnifiedTrace p} {initial : State} {cells : List Cell} {program : List ProgramEntry}
    {projection : SailRV32.instruction → Option (DecoderData UnifiedFamily)}
    (accepted : Accepted trace)
    (inputs : NativeInputs projection trace initial cells program)
    (setup : trace.rom = Setup.table initial)
    (isa : ∃ value, initial.regs.get? .misa = some value)
    {w : Nat → ZMod p} (member : (⟨.machine, w⟩ : Row p UnifiedFamily) ∈ trace.rows)
    {before after : State} {input : Control.Branch.Input} {entry : ProgramEntry}
    (words : Control.Branch.WordMapping input ⟨Control.destination w, Control.finalPC w⟩ w)
    (atRow : input.before = retiredState before (Control.initialPC w).toBitVec)
    (position : RowPosition trace initial cells ⟨.machine, w⟩ input.before)
    (source : entry.SourceWith initial decoderFields)
    (codeAligned : entry.pc.toNat % 4 = 0) (memory : MemoryExecution trace initial cells)
    (query : decoderQuery w = entry.query)
    (encoding : entry.instruction = Control.Branch.instruction input)
    (history : SailHistory cells (rowEvents trace.memoryEpoch (⟨.machine, w⟩ : Row p UnifiedFamily)).reverse before after) :
    ∃ clause, instructionClause entry.instruction = some clause ∧
      run (normalStep clause) (retiredState before (Control.initialPC w).toBitVec) =
        .ok SailRV32.Functions.RETIRE_SUCCESS (retiredState after (Control.finalPC w).toBitVec) := by
  have result := Control.Branch.Proofs.soundness_from_memory hp inverse inputs accepted memory setup member
    words position source query encoding codeAligned isa
  have fields := source.fields
  have metadata : entry.data.mask < 262144 ∧ entry.data.rd = (0#5) := by
    rw [encoding] at fields
    rcases input with ⟨op, left, right, offset, pc, ⟨rs1⟩, ⟨rs2⟩, imm, state⟩
    simp [Control.Branch.instruction, decoderFields, Trace.decoderFields,
      JumpBranchSlt.decoderFields, ShiftBinop.decoderFields, jumpFields, DecoderData.mapFamily] at fields
    rw [← fields]; exact ⟨by norm_num, rfl⟩
  have core := Verification.holds_of_sublist (accepted.constraints _ member)
    (List.sublist_append_left (importedConstraints trace.rom) importedConstraintsTimestampLookups)
  have spec : stepSpec (retiredState before (Control.initialPC w).toBitVec)
      (JumpBranchSlt.Branch.execution input) zeroRegister ⟨Control.destination w, Control.finalPC w⟩ :=
    by
      change stepSpec input.before _ _ _ at result
      rw [atRow] at result
      exact result
  refine ⟨JumpBranchSlt.Branch.execution input, ?_,
    register_retirement (by omega) core fields query metadata.1 metadata.2 trace.memoryEpoch history spec⟩
  rw [encoding]; rfl

theorem branch_execution [Fact p.Prime] [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    (hp : 4194304 ≤ p) (inverse : (-3840 : ZMod p) * 524288 = 1)
    {trace : UnifiedTrace p} {initial : State} {cells : List Cell} {program : List ProgramEntry}
    (accepted : Accepted trace) (decoded : Decoded trace program)
    (inputs : Control.Inputs trace initial cells program)
    (isa : ∃ value, initial.regs.get? .misa = some value)
    {w : Nat → ZMod p} (member : (⟨.machine, w⟩ : Row p UnifiedFamily) ∈ trace.rows)
    {before after : State} {input : Control.Branch.Input} {entry : ProgramEntry}
    (words : Control.Branch.WordMapping input ⟨Control.destination w, Control.finalPC w⟩ w)
    (atRow : input.before = retiredState before (Control.initialPC w).toBitVec)
    (position : RowPosition trace initial cells ⟨.machine, w⟩ input.before)
    (present : entry ∈ program) (query : decoderQuery w = entry.query)
    (encoding : entry.instruction = Control.Branch.instruction input)
    (history : SailHistory cells (rowEvents trace.memoryEpoch (⟨.machine, w⟩ : Row p UnifiedFamily)).reverse before after) :
    ∃ clause, instructionClause entry.instruction = some clause ∧
      run (normalStep clause) (retiredState before (Control.initialPC w).toBitVec) =
        .ok SailRV32.Functions.RETIRE_SUCCESS (retiredState after (Control.finalPC w).toBitVec) := by
  obtain ⟨addresses, image⟩ := inputs.initialization.programImage
  exact branch_execution_from_memory hp inverse accepted inputs.initialization inputs.setup isa member words atRow position
    (run_program_sources image entry present) (inputs.codeAligned entry present)
    (memory_execution (by dsimp [timestampBase]; omega) inverse accepted inputs.initialization decoded)
    query encoding history

theorem comparison_execution_from_memory [Fact p.Prime] [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    (hp : 4194304 ≤ p) (inverse : (-3840 : ZMod p) * 524288 = 1)
    {trace : UnifiedTrace p} {initial : State} {cells : List Cell} {program : List ProgramEntry}
    {projection : SailRV32.instruction → Option (DecoderData UnifiedFamily)}
    (accepted : Accepted trace)
    (inputs : NativeInputs projection trace initial cells program)
    (setup : trace.rom = Setup.table initial)
    {w : Nat → ZMod p} (member : (⟨.machine, w⟩ : Row p UnifiedFamily) ∈ trace.rows)
    {before after : State} {input : Control.Comparison.Input} {entry : ProgramEntry}
    (words : Control.Comparison.WordMapping input ⟨Control.destination w, Control.finalPC w⟩ w)
    (atRow : input.before = retiredState before (Control.initialPC w).toBitVec)
    (position : RowPosition trace initial cells ⟨.machine, w⟩ input.before)
    (source : entry.SourceWith initial decoderFields)
    (codeAligned : entry.pc.toNat % 4 = 0) (memory : MemoryExecution trace initial cells)
    (query : decoderQuery w = entry.query)
    (encoding : entry.instruction = Control.Comparison.instruction input)
    (history : SailHistory cells (rowEvents trace.memoryEpoch (⟨.machine, w⟩ : Row p UnifiedFamily)).reverse before after) :
    ∃ clause, instructionClause entry.instruction = some clause ∧
      run (normalStep clause) (retiredState before (Control.initialPC w).toBitVec) =
        .ok SailRV32.Functions.RETIRE_SUCCESS (retiredState after (Control.finalPC w).toBitVec) := by
  have result := Control.Comparison.Proofs.soundness_from_memory hp inverse inputs accepted memory setup member
    words position source query encoding codeAligned
  have fields := source.fields
  have metadata : entry.data.mask < 262144 ∧ entry.data.rd = match input.rd with | .Regidx bits => bits := by
    rw [encoding] at fields
    rcases input with ⟨op, left, right, pc, ⟨rs1⟩, ⟨rs2⟩, ⟨rd⟩, imm, state⟩
    change BitVec 5 at rs1 rs2 rd
    cases op <;> by_cases zero : rd = (0#5)
    all_goals simp [Control.Comparison.instruction, decoderFields, Trace.decoderFields,
      JumpBranchSlt.decoderFields, ShiftBinop.decoderFields, jumpFields, DecoderData.mapFamily, zero] at fields
    all_goals rw [← fields]
    all_goals exact ⟨by norm_num, rfl⟩
  have core := Verification.holds_of_sublist (accepted.constraints _ member)
    (List.sublist_append_left (importedConstraints trace.rom) importedConstraintsTimestampLookups)
  have spec : stepSpec (retiredState before (Control.initialPC w).toBitVec)
      (JumpBranchSlt.Comparison.execution input) input.rd ⟨Control.destination w, Control.finalPC w⟩ :=
    by
      change stepSpec input.before _ _ _ at result
      rw [atRow] at result
      exact result
  refine ⟨JumpBranchSlt.Comparison.execution input, ?_,
    register_retirement (by omega) core fields query metadata.1 metadata.2 trace.memoryEpoch history spec⟩
  rw [encoding]; cases op : input.opcode <;> simp [Control.Comparison.instruction, instructionClause, JumpBranchSlt.Comparison.execution, op]

theorem comparison_execution [Fact p.Prime] [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    (hp : 4194304 ≤ p) (inverse : (-3840 : ZMod p) * 524288 = 1)
    {trace : UnifiedTrace p} {initial : State} {cells : List Cell} {program : List ProgramEntry}
    (accepted : Accepted trace) (decoded : Decoded trace program)
    (inputs : Control.Inputs trace initial cells program)
    {w : Nat → ZMod p} (member : (⟨.machine, w⟩ : Row p UnifiedFamily) ∈ trace.rows)
    {before after : State} {input : Control.Comparison.Input} {entry : ProgramEntry}
    (words : Control.Comparison.WordMapping input ⟨Control.destination w, Control.finalPC w⟩ w)
    (atRow : input.before = retiredState before (Control.initialPC w).toBitVec)
    (position : RowPosition trace initial cells ⟨.machine, w⟩ input.before)
    (present : entry ∈ program) (query : decoderQuery w = entry.query)
    (encoding : entry.instruction = Control.Comparison.instruction input)
    (history : SailHistory cells (rowEvents trace.memoryEpoch (⟨.machine, w⟩ : Row p UnifiedFamily)).reverse before after) :
    ∃ clause, instructionClause entry.instruction = some clause ∧
      run (normalStep clause) (retiredState before (Control.initialPC w).toBitVec) =
        .ok SailRV32.Functions.RETIRE_SUCCESS (retiredState after (Control.finalPC w).toBitVec) := by
  obtain ⟨addresses, image⟩ := inputs.initialization.programImage
  exact comparison_execution_from_memory hp inverse accepted inputs.initialization inputs.setup member words atRow position
    (run_program_sources image entry present) (inputs.codeAligned entry present)
    (memory_execution (by dsimp [timestampBase]; omega) inverse accepted inputs.initialization decoded)
    query encoding history

theorem jump_execution_from_memory [Fact p.Prime] [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    (hp : 4194304 ≤ p) (inverse : (-3840 : ZMod p) * 524288 = 1)
    {trace : UnifiedTrace p} {initial : State} {cells : List Cell} {program : List ProgramEntry}
    {projection : SailRV32.instruction → Option (DecoderData UnifiedFamily)}
    (accepted : Accepted trace)
    {w : Nat → ZMod p} (member : (⟨.machine, w⟩ : Row p UnifiedFamily) ∈ trace.rows)
    {before after : State} {input : Jump.Input} {entry : ProgramEntry}
    (inputs : NativeInputs projection trace initial cells program)
    (setup : trace.rom = Setup.table initial)
    (isa : ∃ value, initial.regs.get? .misa = some value)
    (landingPad : input.instruction.indirect = true →
      initial.regs.get? .cur_privilege = some .Machine ∧
        ∃ security, initial.regs.get? .mseccfg = some security ∧
          SailRV32.Functions._get_Seccfg_MLPE security = 0)
    (words : Jump.WordMapping input ⟨Control.destination w, Control.finalPC w⟩ w)
    (atRow : input.before = retiredState before (Control.initialPC w).toBitVec)
    (position : RowPosition trace initial cells ⟨.machine, w⟩ input.before)
    (source : entry.SourceWith initial decoderFields)
    (codeAligned : entry.pc.toNat % 4 = 0) (memory : MemoryExecution trace initial cells)
    (query : decoderQuery w = entry.query)
    (encoding : entry.instruction = Jump.instruction input)
    (history : SailHistory cells (rowEvents trace.memoryEpoch (⟨.machine, w⟩ : Row p UnifiedFamily)).reverse before after) :
    ∃ clause, instructionClause entry.instruction = some clause ∧
      run (normalStep clause) (retiredState before (Control.initialPC w).toBitVec) =
        .ok SailRV32.Functions.RETIRE_SUCCESS (retiredState after (Control.finalPC w).toBitVec) := by
  have result := Jump.Proofs.soundness_from_memory hp inverse inputs accepted memory setup member
    words position source query encoding codeAligned isa landingPad
  have fields := source.fields
  have metadata : entry.data.mask < 262144 ∧ entry.data.rd = match input.rd with | .Regidx bits => bits := by
    rw [encoding] at fields
    rcases input with ⟨op, source, offset, pc, ⟨rs1⟩, ⟨rd⟩, state⟩
    change BitVec 5 at rs1 rd
    cases op <;> by_cases zero : rd = (0#5)
    all_goals simp [Jump.instruction, decoderFields, Trace.decoderFields,
      JumpBranchSlt.decoderFields, ShiftBinop.decoderFields, jumpFields, DecoderData.mapFamily, zero] at fields
    all_goals rw [← fields]
    all_goals simp [zero]
  have core := Verification.holds_of_sublist (accepted.constraints _ member)
    (List.sublist_append_left (importedConstraints trace.rom) importedConstraintsTimestampLookups)
  have spec : stepSpec (retiredState before (Control.initialPC w).toBitVec)
      (JumpBranchSlt.Jump.execution input) input.rd ⟨Control.destination w, Control.finalPC w⟩ :=
    by
      change stepSpec input.before _ _ _ at result
      rw [atRow] at result
      exact result
  refine ⟨JumpBranchSlt.Jump.execution input, ?_,
    register_retirement (by omega) core fields query metadata.1 metadata.2 trace.memoryEpoch history spec⟩
  rw [encoding]; cases op : input.instruction <;> simp [Jump.instruction, instructionClause, JumpBranchSlt.Jump.execution, op]

theorem jump_execution [Fact p.Prime] [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    (hp : 4194304 ≤ p) (inverse : (-3840 : ZMod p) * 524288 = 1)
    {trace : UnifiedTrace p} {initial : State} {cells : List Cell} {program : List ProgramEntry}
    (accepted : Accepted trace) (decoded : Decoded trace program)
    {w : Nat → ZMod p} (member : (⟨.machine, w⟩ : Row p UnifiedFamily) ∈ trace.rows)
    {before after : State} {input : Jump.Input} {entry : ProgramEntry}
    (inputs : Jump.InterfaceAssumptions trace initial cells program input ⟨Control.destination w, Control.finalPC w⟩ w)
    (words : Jump.WordMapping input ⟨Control.destination w, Control.finalPC w⟩ w)
    (atRow : input.before = retiredState before (Control.initialPC w).toBitVec)
    (position : RowPosition trace initial cells ⟨.machine, w⟩ input.before)
    (present : entry ∈ program) (query : decoderQuery w = entry.query)
    (encoding : entry.instruction = Jump.instruction input)
    (history : SailHistory cells (rowEvents trace.memoryEpoch (⟨.machine, w⟩ : Row p UnifiedFamily)).reverse before after) :
    ∃ clause, instructionClause entry.instruction = some clause ∧
      run (normalStep clause) (retiredState before (Control.initialPC w).toBitVec) =
        .ok SailRV32.Functions.RETIRE_SUCCESS (retiredState after (Control.finalPC w).toBitVec) := by
  obtain ⟨addresses, image⟩ := inputs.initialization.programImage
  exact jump_execution_from_memory hp inverse accepted member inputs.initialization inputs.setup inputs.isa inputs.landingPad words atRow position
    (run_program_sources image entry present) (inputs.codeAligned entry present)
    (memory_execution (by dsimp [timestampBase]; omega) inverse accepted inputs.initialization decoded)
    query encoding history

end Airbender.UnifiedReduced.Proofs
