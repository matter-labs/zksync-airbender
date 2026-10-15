import Airbender.Review.Trace.UnifiedReduced.MixedCycles
import Airbender.Proofs.UnifiedReduced.MixedComposition
import Airbender.Proofs.UnifiedReduced.MixedCustomRetirement
import Airbender.Proofs.UnifiedReduced.MixedControlRetirement
import Airbender.Proofs.UnifiedReduced.MixedComparisonRetirement
import Airbender.Proofs.UnifiedReduced.MixedBinaryRetirement
import Airbender.Proofs.UnifiedReduced.MixedRAMRetirement
import Airbender.Proofs.UnifiedReduced.CallerCycles
import Airbender.Proofs.UnifiedReduced.WorkerExecution

namespace Airbender.UnifiedReduced.Caller.Proofs
open Arithmetic Reference.RiscV Reference.RiscV.Sail Reference.Sail Trace Trace.Proofs
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

set_option backward.isDefEq.respectTransparency false in
theorem ordinary_cycle_at [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {initial : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    (accepted : MixedMemoryAccepted data program) (inputs : MixedMemoryInputs data program initial ca oa cells)
    (profile : RetirementProfile data program initial cells)
    (effects : MixedMemoryEffects data initial cells)
    {events : List MemoryAccess} {finalState : State}
    (permutation : events.Perm (data.mixedSteps.map transferEvent))
    (order : events.Pairwise (fun a b => b.1 ≤ a.1))
    (history : SailHistory cells events initial finalState)
    {row : Trace.Row babyBearModulus UnifiedFamily}
    (member : row ∈ data.machine.rows) (ordinary : row ∉ data.callers) :
    OrdinaryCycle program cells events initial finalState row := by
  obtain ⟨entry, present, _, query⟩ := decoder_member (accepted.ordinaryDecoded row member ordinary)
  have source := run_program_sources inputs.ordinaryProgram entry present
  refine ⟨entry, present, query, ?_⟩
  cases row with
  | mk kind w =>
    cases kind
    change decoderQuery w = entry.query at query
    rcases Mixed.Proofs.fields_cases source.fields with standard | custom
    · obtain ⟨observation, observed⟩ := UnifiedReduced.Proofs.observe_supported w initial standard
      have liftClause {clause : SailRV32.SailM SailRV32.ExecutionResult}
          (selected : instructionClause entry.instruction = some clause) :
          Mixed.clauseFor entry.instruction = some clause := by
        simp [Mixed.clauseFor, selected]
      cases observation with
      | arithmetic input =>
        obtain ⟨encoding, _, words⟩ := UnifiedReduced.Proofs.observe_arithmetic observed
        refine ⟨Sail.execution input, liftClause ?_, ?_⟩
        · rw [encoding]; exact UnifiedReduced.Proofs.arithmetic_clause input
        · exact mixed_arithmetic_cycle_at accepted inputs effects permutation order history member
            (words (UnifiedReduced.Proofs.arithmetic_index standard encoding query))
            (fun index _ => profile.registers index) ⟨entry, present, query, encoding⟩
      | branch input =>
        obtain ⟨encoding, _, words⟩ := UnifiedReduced.Proofs.observe_branch observed
        refine ⟨JumpBranchSlt.Branch.execution input, liftClause ?_, ?_⟩
        · rw [encoding]; rfl
        · exact mixed_branch_cycle_at accepted inputs effects permutation order history profile.configuration.isa
            member words ⟨entry, present, query, encoding, (profile.code.ordinary entry present).2⟩
      | comparison input =>
        obtain ⟨encoding, _, words⟩ := UnifiedReduced.Proofs.observe_comparison observed
        refine ⟨JumpBranchSlt.Comparison.execution input, liftClause ?_, ?_⟩
        · rw [encoding]
          cases op : input.opcode <;>
            simp [Control.Comparison.instruction, instructionClause, Reference.RiscV.Sail.registerClause,
              JumpBranchSlt.Comparison.execution, JumpBranchSlt.Comparison.instruction, Option.get_some, op]
        · exact mixed_comparison_cycle_at accepted inputs effects permutation order history
            member words ⟨entry, present, query, encoding, (profile.code.ordinary entry present).2⟩
      | jump input =>
        obtain ⟨encoding, _, words⟩ := UnifiedReduced.Proofs.observe_jump observed
        refine ⟨JumpBranchSlt.Jump.execution input, liftClause ?_, ?_⟩
        · rw [encoding]
          cases kind : input.instruction <;>
            simp [Jump.instruction, JumpBranchSlt.Jump.instruction, JumpBranchSlt.Jump.execution,
              instructionClause, Reference.RiscV.Sail.registerClause, Option.get_some, kind]
        · apply mixed_jump_cycle_at accepted inputs effects permutation order history profile.configuration.isa
            (input := input) _ member words ⟨entry, present, query, encoding, (profile.code.ordinary entry present).2⟩
          intro indirect
          refine ⟨profile.configuration.privilege, profile.landingPadDisabled ?_⟩
          cases kind : input.instruction with
          | jal imm => simp [JumpBranchSlt.Jump.Instruction.indirect, kind] at indirect
          | jalr imm => exact ⟨entry, present, imm, input.rs1, input.rd,
              by simpa [Jump.instruction, JumpBranchSlt.Jump.instruction, kind] using encoding⟩
      | binary shift input =>
        obtain ⟨encoding, _, words⟩ := UnifiedReduced.Proofs.observe_binary observed
        refine ⟨ShiftBinop.execution input, liftClause ?_, ?_⟩
        · rcases input with ⟨op, immediate, left, right, pc, rs1, rs2, rd, imm, state⟩
          cases shift <;> cases op <;> cases immediate
          all_goals simp [Shift.instruction, Binary.instruction] at encoding
          all_goals rw [← encoding]
          all_goals rfl
        · exact mixed_binary_cycle_at accepted inputs effects permutation order history shift
            member words ⟨entry, present, query, encoding⟩
      | memory input =>
        obtain ⟨encoding, _, words⟩ := UnifiedReduced.Proofs.observe_memory observed
        have destination : input.store = false → input.rd ≠ zeroRegister := by
          intro load zero
          cases rs : input.rs1 with
          | Regidx index =>
            apply profile.loads entry present input.encodedImmediate index
            simpa only [load, Bool.false_eq_true, if_false, zero, rs, zeroRegister] using encoding
        refine ⟨Airbender.WordMemory.execution input, liftClause ?_, ?_⟩
        · rw [encoding]
          cases mode : input.store <;>
            simp [Airbender.WordMemory.execution, Airbender.WordMemory.instruction,
              Trace.instructionClause, Option.get_some, mode, instructionClause]
        · exact mixed_ram_cycle_at accepted inputs effects permutation order history
            profile.configuration profile.ordinary profile.code.ram destination member words
            ⟨entry, present, query, encoding⟩
    · have supported : Custom.clauseFor entry.instruction ≠ none := by
        obtain arithmetic | rotation := UnifiedReduced.Proofs.custom_instruction_cases custom
        · obtain ⟨rs1, rs2, rd, encoding⟩ := arithmetic
          rw [encoding]; simp [Custom.clauseFor]
        · obtain ⟨kind, rs1, rd, encoding⟩ := rotation
          rw [encoding]; fin_cases kind <;> simp [Custom.clauseFor, XorRotate.amount]
      obtain ⟨clause, selected, retired⟩ := mixed_custom_cycle_at accepted inputs effects permutation order history
        member present query supported
      exact ⟨clause, by simp [Mixed.clauseFor, Mixed.Proofs.custom_no_standard_clause custom, selected], retired⟩

theorem mixed_cycle_effects_at [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {initial : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    (accepted : MixedMemoryAccepted data program) (inputs : MixedMemoryInputs data program initial ca oa cells)
    (effects : MixedMemoryEffects data initial cells)
    {events : List MemoryAccess} {finalState : State}
    (permutation : events.Perm (data.mixedSteps.map transferEvent))
    (order : events.Pairwise (fun a b => b.1 ≤ a.1))
    (history : SailHistory cells events initial finalState)
    (code : CodeProfile data program cells)
    (ordinary : ∀ row ∈ data.machine.rows, row ∉ data.callers →
      OrdinaryCycle program cells events initial finalState row)
    (terminal : ∀ token ∈ data.machine.terminalMemory, ∃ cell ∈ cells,
      cell.addressCode = token.address ∧ cell.read finalState = .ok token.word.toBitVec finalState) :
    MixedCycleEffects data program initial cells := by
  refine ⟨effects.requests,
    state_path_checks (by decide) (by decide) accepted.constraints accepted.states
      inputs.publicProgram.initialClock inputs.publicProgram.initialAligned,
    events, finalState, permutation, order, history,
    current_fetch_of_history accepted inputs code order history, ordinary,
    native_caller_cycles_at accepted inputs code effects permutation order history,
    all_worker_execution (by decide) (by decide) accepted inputs.publicProgram
      inputs.initialization inputs.distinct inputs.aligned permutation order history,
    retired_state_pc finalState _, ?_⟩
  intro token member
  obtain ⟨cell, present, address, read⟩ := terminal token member
  exact ⟨cell, present, address, cell_read_PC cell (cell_read_nextPC cell read _) _⟩

theorem mixed_cycle_effects [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {initial : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    (accepted : MixedMemoryAccepted data program) (inputs : MixedMemoryInputs data program initial ca oa cells)
    (profile : RetirementProfile data program initial cells) :
    MixedCycleEffects data program initial cells := by
  have effects := mixed_memory_effects accepted inputs
  obtain ⟨events, finalState, permutation, order, history, _, _, terminal⟩ := effects.execution
  exact mixed_cycle_effects_at accepted inputs effects permutation order history profile.code
    (fun _ member ordinary => ordinary_cycle_at accepted inputs profile effects permutation order history member ordinary)
    terminal

end Airbender.UnifiedReduced.Caller.Proofs
