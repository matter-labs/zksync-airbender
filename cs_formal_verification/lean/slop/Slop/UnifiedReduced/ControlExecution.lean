import Slop.UnifiedReduced.RegisterRetirement
import Slop.UnifiedReduced.BranchSoundness
import Slop.UnifiedReduced.ComparisonSoundness
import Slop.UnifiedReduced.JumpSoundness

namespace Airbender.UnifiedReduced.Proofs
open Arithmetic Reference.RiscV Reference.RiscV.Sail Reference.Sail Trace Trace.Proofs
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

theorem branch_metadata {input : Control.Branch.Input} {entry : ProgramEntry}
    (encoding : entry.instruction = Control.Branch.instruction input)
    (fields : decoderFields entry.instruction = some entry.data) :
    entry.data.mask = 24576 ∧ entry.data.rd = (0#5) := by
  rw [encoding] at fields
  rcases input with ⟨op, left, right, offset, pc, ⟨rs1⟩, ⟨rs2⟩, imm, state⟩
  simp [Control.Branch.instruction, JumpBranchSlt.Branch.instruction, decoderFields, Trace.decoderFields,
    JumpBranchSlt.decoderFields, ShiftBinop.decoderFields, jumpFields, DecoderData.mapFamily] at fields
  rw [← fields]; exact ⟨rfl, rfl⟩

theorem branch_register_retirement [Fact p.Prime] (hp : 524288 < p)
    {setup : Table (ZMod p) (fields 10)} {cells : List Cell} {w : Nat → ZMod p}
    {input : Control.Branch.Input} {entry : ProgramEntry}
    (core : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (fields : decoderFields entry.instruction = some entry.data) (query : decoderQuery w = entry.query)
    (encoding : entry.instruction = Control.Branch.instruction input)
    (epoch : Nat) {before after : State}
    (history : SailHistory cells (rowEvents epoch (⟨.machine, w⟩ : Row p UnifiedFamily)).reverse before after)
    (spec : stepSpec (retiredState before (Control.initialPC w).toBitVec)
      (JumpBranchSlt.Branch.execution input) zeroRegister ⟨Control.destination w, Control.finalPC w⟩) :
    run (normalStep (JumpBranchSlt.Branch.execution input)) (retiredState before (Control.initialPC w).toBitVec) =
      .ok SailRV32.Functions.RETIRE_SUCCESS (retiredState after (Control.finalPC w).toBitVec) := by
  have metadata := branch_metadata encoding fields
  exact register_retirement hp core fields query (by rw [metadata.1]; decide) metadata.2 epoch history spec

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
  have core := Verification.holds_of_sublist (accepted.constraints _ member)
    (List.sublist_append_left (importedConstraints trace.rom) importedConstraintsTimestampLookups)
  have spec : stepSpec (retiredState before (Control.initialPC w).toBitVec)
      (JumpBranchSlt.Branch.execution input) zeroRegister ⟨Control.destination w, Control.finalPC w⟩ :=
    by
      change stepSpec input.before _ _ _ at result
      rw [atRow] at result
      exact result
  refine ⟨JumpBranchSlt.Branch.execution input, ?_,
    branch_register_retirement (by omega) core fields query encoding trace.memoryEpoch history spec⟩
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

theorem comparison_metadata {input : Control.Comparison.Input} {entry : ProgramEntry}
    (encoding : entry.instruction = Control.Comparison.instruction input)
    (fields : decoderFields entry.instruction = some entry.data) :
    entry.data.mask = 4096 ∧ entry.data.rd = match input.rd with | .Regidx bits => bits := by
  rw [encoding] at fields
  rcases input with ⟨op, left, right, pc, ⟨rs1⟩, ⟨rs2⟩, ⟨rd⟩, imm, state⟩
  change BitVec 5 at rs1 rs2 rd
  cases op <;> by_cases zero : rd = (0#5)
  all_goals simp [Control.Comparison.instruction, JumpBranchSlt.Comparison.instruction, decoderFields, Trace.decoderFields,
    JumpBranchSlt.decoderFields, ShiftBinop.decoderFields, jumpFields, DecoderData.mapFamily, zero] at fields
  all_goals rw [← fields]
  all_goals exact ⟨rfl, rfl⟩

theorem comparison_register_retirement [Fact p.Prime] (hp : 524288 < p)
    {setup : Table (ZMod p) (fields 10)} {cells : List Cell} {w : Nat → ZMod p}
    {input : Control.Comparison.Input} {entry : ProgramEntry}
    (core : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (fields : decoderFields entry.instruction = some entry.data) (query : decoderQuery w = entry.query)
    (encoding : entry.instruction = Control.Comparison.instruction input)
    (epoch : Nat) {before after : State}
    (history : SailHistory cells (rowEvents epoch (⟨.machine, w⟩ : Row p UnifiedFamily)).reverse before after)
    (spec : stepSpec (retiredState before (Control.initialPC w).toBitVec)
      (JumpBranchSlt.Comparison.execution input) input.rd ⟨Control.destination w, Control.finalPC w⟩) :
    run (normalStep (JumpBranchSlt.Comparison.execution input)) (retiredState before (Control.initialPC w).toBitVec) =
      .ok SailRV32.Functions.RETIRE_SUCCESS (retiredState after (Control.finalPC w).toBitVec) := by
  have metadata := comparison_metadata encoding fields
  exact register_retirement hp core fields query (by rw [metadata.1]; decide) metadata.2 epoch history spec

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
  have core := Verification.holds_of_sublist (accepted.constraints _ member)
    (List.sublist_append_left (importedConstraints trace.rom) importedConstraintsTimestampLookups)
  have spec : stepSpec (retiredState before (Control.initialPC w).toBitVec)
      (JumpBranchSlt.Comparison.execution input) input.rd ⟨Control.destination w, Control.finalPC w⟩ :=
    by
      change stepSpec input.before _ _ _ at result
      rw [atRow] at result
      exact result
  refine ⟨JumpBranchSlt.Comparison.execution input, ?_,
    comparison_register_retirement (by omega) core fields query encoding trace.memoryEpoch history spec⟩
  rw [encoding]; cases op : input.opcode <;> simp [Control.Comparison.instruction, instructionClause, Reference.RiscV.Sail.registerClause, JumpBranchSlt.Comparison.execution, JumpBranchSlt.Comparison.instruction, Reference.RiscV.Sail.registerClause, Option.get_some, op, Option.get_some]

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

theorem jump_metadata {input : Jump.Input} {entry : ProgramEntry}
    (encoding : entry.instruction = Jump.instruction input)
    (fields : decoderFields entry.instruction = some entry.data) :
    entry.data.mask = (if input.instruction.indirect then 2048 else 1024) +
      (if input.rd = zeroRegister then 16384 else 0) ∧ entry.data.rd = match input.rd with | .Regidx bits => bits := by
  rw [encoding] at fields
  rcases input with ⟨op, source, offset, pc, ⟨rs1⟩, ⟨rd⟩, state⟩
  change BitVec 5 at rs1 rd
  cases op <;> by_cases zero : rd = (0#5)
  all_goals simp [Jump.instruction, JumpBranchSlt.Jump.instruction, decoderFields, Trace.decoderFields,
    JumpBranchSlt.decoderFields, ShiftBinop.decoderFields, jumpFields, DecoderData.mapFamily, zero] at fields
  all_goals rw [← fields]
  all_goals simp [zero, JumpBranchSlt.Jump.Instruction.indirect, zeroRegister]

theorem jump_register_retirement [Fact p.Prime] (hp : 524288 < p)
    {setup : Table (ZMod p) (fields 10)} {cells : List Cell} {w : Nat → ZMod p}
    {input : Jump.Input} {entry : ProgramEntry}
    (core : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (fields : decoderFields entry.instruction = some entry.data) (query : decoderQuery w = entry.query)
    (encoding : entry.instruction = Jump.instruction input)
    (epoch : Nat) {before after : State}
    (history : SailHistory cells (rowEvents epoch (⟨.machine, w⟩ : Row p UnifiedFamily)).reverse before after)
    (spec : stepSpec (retiredState before (Control.initialPC w).toBitVec)
      (JumpBranchSlt.Jump.execution input) input.rd ⟨Control.destination w, Control.finalPC w⟩) :
    run (normalStep (JumpBranchSlt.Jump.execution input)) (retiredState before (Control.initialPC w).toBitVec) =
      .ok SailRV32.Functions.RETIRE_SUCCESS (retiredState after (Control.finalPC w).toBitVec) := by
  have metadata := jump_metadata encoding fields
  have mask : entry.data.mask < 262144 := by
    rw [metadata.1]; split <;> split <;> decide
  exact register_retirement hp core fields query mask metadata.2 epoch history spec

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
  have core := Verification.holds_of_sublist (accepted.constraints _ member)
    (List.sublist_append_left (importedConstraints trace.rom) importedConstraintsTimestampLookups)
  have spec : stepSpec (retiredState before (Control.initialPC w).toBitVec)
      (JumpBranchSlt.Jump.execution input) input.rd ⟨Control.destination w, Control.finalPC w⟩ :=
    by
      change stepSpec input.before _ _ _ at result
      rw [atRow] at result
      exact result
  refine ⟨JumpBranchSlt.Jump.execution input, ?_,
    jump_register_retirement (by omega) core fields query encoding trace.memoryEpoch history spec⟩
  rw [encoding]; cases op : input.instruction <;> simp [Jump.instruction, instructionClause, Reference.RiscV.Sail.registerClause, JumpBranchSlt.Jump.execution, JumpBranchSlt.Jump.instruction, Reference.RiscV.Sail.registerClause, Option.get_some, op, Option.get_some]

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
