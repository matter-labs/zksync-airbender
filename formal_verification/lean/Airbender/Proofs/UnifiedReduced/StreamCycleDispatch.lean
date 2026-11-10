import Airbender.Proofs.UnifiedReduced.StreamOrdinaryCycles
import Airbender.Proofs.UnifiedReduced.StreamReadTag

namespace Airbender.UnifiedReduced.Caller.Stream.Proofs
open Arithmetic Reference.RiscV Reference.RiscV.Sail Reference.Sail Trace Trace.Proofs
open Caller.Proofs
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- Standard and custom public sources select their exact native cycle proof. -/
theorem mixed_cycle_at [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {initial : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    (accepted : MixedMemoryAccepted data program)
    (inputs : NativeMemoryInputsWith Stream.decoderFields data program initial ca oa cells)
    (profile : RetirementProfile data program initial cells)
    (effects : MixedMemoryEffects data initial cells)
    {events : List MemoryAccess} {finalState : State}
    (permutation : events.Perm (data.mixedSteps.map transferEvent))
    (order : events.Pairwise (fun a b => b.1 ≤ a.1))
    (history : SailHistory cells events initial finalState)
    {w : Nat → ZMod babyBearModulus}
    (member : (⟨.machine, w⟩ : Trace.Row babyBearModulus UnifiedFamily) ∈ data.machine.rows)
    {entry : UnifiedReduced.ProgramEntry} (present : entry ∈ program)
    (source : entry.SourceWith initial Mixed.decoderFields)
    (query : decoderQuery w = entry.query) :
    ∃ clause, Mixed.clauseFor entry.instruction = some clause ∧
      RetiresCycle cells events initial finalState
        (⟨.machine, w⟩ : Trace.Row babyBearModulus UnifiedFamily) clause := by
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
      · exact arithmetic_cycle_at accepted inputs effects permutation order history member
          (words (UnifiedReduced.Proofs.arithmetic_index standard encoding query))
          (fun index _ => profile.registers index) standard query encoding
    | branch input =>
      obtain ⟨encoding, _, words⟩ := UnifiedReduced.Proofs.observe_branch observed
      refine ⟨JumpBranchSlt.Branch.execution input, liftClause ?_, ?_⟩
      · rw [encoding]; rfl
      · exact branch_cycle_at accepted inputs effects permutation order history profile.configuration.isa
          member words ⟨entry, present, source, query, encoding, (profile.code.ordinary entry present).2⟩
    | comparison input =>
      obtain ⟨encoding, _, words⟩ := UnifiedReduced.Proofs.observe_comparison observed
      refine ⟨JumpBranchSlt.Comparison.execution input, liftClause ?_, ?_⟩
      · rw [encoding]
        cases op : input.opcode <;>
          simp [Control.Comparison.instruction, instructionClause, Reference.RiscV.Sail.registerClause,
            JumpBranchSlt.Comparison.execution, JumpBranchSlt.Comparison.instruction, Option.get_some, op]
      · exact comparison_cycle_at accepted inputs effects permutation order history
          member words ⟨entry, present, source, query, encoding, (profile.code.ordinary entry present).2⟩
    | jump input =>
      obtain ⟨encoding, _, words⟩ := UnifiedReduced.Proofs.observe_jump observed
      refine ⟨JumpBranchSlt.Jump.execution input, liftClause ?_, ?_⟩
      · rw [encoding]
        cases kind : input.instruction <;>
          simp [Jump.instruction, JumpBranchSlt.Jump.instruction, JumpBranchSlt.Jump.execution,
            instructionClause, Reference.RiscV.Sail.registerClause, Option.get_some, kind]
      · apply jump_cycle_at accepted inputs effects permutation order history profile.configuration.isa
          (input := input) _ member words ⟨entry, present, source, query, encoding, (profile.code.ordinary entry present).2⟩
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
      · exact binary_cycle_at accepted inputs effects permutation order history shift
          member words ⟨entry, present, source, query, encoding⟩
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
      · exact ram_cycle_at accepted inputs effects permutation order history
          profile.configuration profile.ordinary profile.code.ram destination member words
          ⟨entry, present, source, query, encoding⟩
  · obtain ⟨clause, selected, retired⟩ := custom_cycle_at accepted inputs effects permutation order history
      member custom query
    exact ⟨clause, by simp [Mixed.clauseFor, Mixed.Proofs.custom_no_standard_clause custom, selected], retired⟩

/-- One public clause dispatch covers every noncaller in the stream registry. -/
theorem ordinary_cycle_at [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {initial : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    (accepted : MixedMemoryAccepted data program)
    (inputs : NativeMemoryInputsWith Stream.decoderFields data program initial ca oa cells)
    (profile : RetirementProfile data program initial cells)
    (effects : MixedMemoryEffects data initial cells)
    {events : List MemoryAccess} {finalState : State}
    (permutation : events.Perm (data.mixedSteps.map transferEvent))
    (order : events.Pairwise (fun a b => b.1 ≤ a.1))
    (history : SailHistory cells events initial finalState)
    (stream : List (BitVec 32)) (ports : Stream.StreamPorts data.machine stream)
    {row : Trace.Row babyBearModulus UnifiedFamily}
    (member : row ∈ data.machine.rows) (ordinary : row ∉ data.callers) :
    ∃ entry ∈ program, row.decoderQuery = entry.query ∧ ∃ clause next,
      Stream.clauseFor stream
        (ExternalStream.index Trace.Row.clock Stream.isRead data.machine.rows row)
        entry.instruction = some (clause, next) ∧
      next = ExternalStream.index Trace.Row.clock Stream.isRead data.machine.rows row +
        (if Stream.isRead row then 1 else 0) ∧
      RetiresCycle cells events initial finalState row clause := by
  obtain ⟨entry, present, _, query⟩ :=
    decoder_member (accepted.ordinaryDecoded row member ordinary)
  have source := run_program_sources inputs.ordinaryProgram entry present
  refine ⟨entry, present, query, ?_⟩
  cases row with
  | mk family w =>
    cases family
    change decoderQuery w = entry.query at query
    have core := Verification.holds_of_sublist (accepted.constraints _ member)
      (List.sublist_append_left (importedConstraints data.machine.rom)
        importedConstraintsTimestampLookups)
    rcases fields_cases source.fields with modular | external
    · have unchanged := native_modular_read_disabled (by decide) core modular query
      rcases Modular.Proofs.fields_cases modular with mixed | mop
      · obtain ⟨clause, selected, retired⟩ := mixed_cycle_at accepted inputs profile
          effects permutation order history member present
          ⟨source.bytes, source.decoded, mixed⟩ query
        refine ⟨clause, ExternalStream.index Trace.Row.clock Stream.isRead data.machine.rows
          (⟨.machine, w⟩ : Trace.Row babyBearModulus UnifiedFamily), ?_, by simp [unchanged], retired⟩
        simp [Stream.clauseFor, Modular.clauseFor, selected]
      · obtain ⟨clause, selected, retired⟩ := modular_cycle_at accepted inputs
          profile.registers effects permutation order history member ordinary mop query
        have absent : Mixed.clauseFor entry.instruction = none := by
          obtain ⟨opcode, rs1, rs2, rd, encoding, _⟩ := Modular.Proofs.mop_cases mop
          rw [encoding]
          cases opcode <;> rfl
        refine ⟨clause, ExternalStream.index Trace.Row.clock Stream.isRead data.machine.rows
          (⟨.machine, w⟩ : Trace.Row babyBearModulus UnifiedFamily), ?_, by simp [unchanged], retired⟩
        simp [Stream.clauseFor, Modular.clauseFor, absent, selected]
    · obtain ⟨clause, next, selected, counter, retired⟩ := external_cycle_at accepted
        inputs effects permutation order history member ordinary external query stream
        (ExternalStream.index Trace.Row.clock Stream.isRead data.machine.rows
          (⟨.machine, w⟩ : Trace.Row babyBearModulus UnifiedFamily)) (by
            intro read
            simpa [Stream.response, write_word, importedConstraintsMemoryPorts,
              Control.destination] using ports _ member read)
      have absent : Modular.clauseFor entry.instruction = none := by
        rcases external_fields_cases external with ⟨_, _, encoding, _⟩ | ⟨_, _, encoding, _⟩
        all_goals rw [encoding]; rfl
      exact ⟨clause, next, by simp [Stream.clauseFor, absent, selected], counter, retired⟩

end Airbender.UnifiedReduced.Caller.Stream.Proofs
