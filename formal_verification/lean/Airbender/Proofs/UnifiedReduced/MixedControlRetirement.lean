import Airbender.Proofs.UnifiedReduced.MixedRetirement
import Airbender.Proofs.UnifiedReduced.ControlExecution

namespace Airbender.UnifiedReduced.Caller.Proofs
open Arithmetic Reference.RiscV Reference.RiscV.Sail Reference.Sail Trace Trace.Proofs
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

theorem branch_fields {input : Control.Branch.Input} {entry : UnifiedReduced.ProgramEntry}
    (fields : Mixed.decoderFields entry.instruction = some entry.data)
    (encoding : entry.instruction = Control.Branch.instruction input) :
    UnifiedReduced.decoderFields entry.instruction = some entry.data := by
  rcases Mixed.Proofs.fields_cases fields with standard | custom
  · exact standard
  · rw [encoding] at custom
    simp [Control.Branch.instruction, JumpBranchSlt.Branch.instruction, customDecoderFields] at custom

theorem mixed_branch_cycle_at
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {initial : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    (accepted : MixedMemoryAccepted data program) (inputs : MixedMemoryInputs data program initial ca oa cells)
    (effects : MixedMemoryEffects data initial cells)
    {events : List MemoryAccess} {finalState : State}
    (permutation : events.Perm (data.mixedSteps.map transferEvent))
    (order : events.Pairwise (fun a b => b.1 ≤ a.1))
    (history : SailHistory cells events initial finalState)
    (isa : ∃ value, initial.regs.get? .misa = some value)
    {w : Nat → ZMod babyBearModulus} {input : Control.Branch.Input}
    (member : (⟨.machine, w⟩ : Trace.Row babyBearModulus UnifiedFamily) ∈ data.machine.rows)
    (words : Control.Branch.WordMapping input ⟨Control.destination w, Control.finalPC w⟩ w)
    (instruction : ∃ entry ∈ program, decoderQuery w = entry.query ∧
      entry.instruction = Control.Branch.instruction input ∧ entry.pc.toNat % 4 = 0) :
      RetiresCycle cells events initial finalState (⟨.machine, w⟩ : Trace.Row babyBearModulus UnifiedFamily)
        (JumpBranchSlt.Branch.execution input) := by
  obtain ⟨entry, present, query, encoding, aligned⟩ := instruction
  have source := run_program_sources inputs.ordinaryProgram entry present
  have fields := branch_fields source.fields encoding
  have standardSource : entry.SourceWith initial UnifiedReduced.decoderFields := ⟨source.bytes, source.decoded, fields⟩
  have core := Verification.holds_of_sublist (accepted.constraints _ member)
    (List.sublist_append_left (importedConstraints data.machine.rom) importedConstraintsTimestampLookups)
  have metadata := UnifiedReduced.Proofs.branch_metadata encoding fields
  have ordinary : (⟨.machine, w⟩ : Trace.Row babyBearModulus UnifiedFamily) ∉ data.callers := by
    apply ordinary_of_decoder_mask (by decide) core fields query
    rw [metadata.1]
    decide
  obtain ⟨before, after, past, current, future, native, ranges⟩ :=
    ordinary_cycle_context_at accepted inputs effects permutation order history member ordinary
  have leftRange := ranges importedConstraintsMemoryPorts[0]
    (by simp [Trace.Row.ports, CircuitLayout.ports, importedConstraintsMemoryPorts])
  have rightRange := ranges importedConstraintsMemoryPorts[1]
    (by simp [Trace.Row.ports, CircuitLayout.ports, importedConstraintsMemoryPorts])
  let actualInput : Control.Branch.Input := {input with before := retiredState before (Control.initialPC w).toBitVec}
  have actualWords : Control.Branch.WordMapping actualInput ⟨Control.destination w, Control.finalPC w⟩ w :=
    ⟨words.left, words.right, words.offset, words.pc, words.result, words.nextPC⟩
  have actualEncoding : entry.instruction = Control.Branch.instruction actualInput := by
    simpa only [Control.Branch.instruction, JumpBranchSlt.Branch.instruction, actualInput] using encoding
  have pcRead : run (SailRV32.Functions.get_arch_pc ()) actualInput.before =
      .ok actualInput.pc.toBitVec actualInput.before := by
    rw [show actualInput.pc = Control.initialPC w from words.pc]
    exact retired_state_pc before _
  have spec := Control.Branch.Proofs.soundness_from_history (by decide) core (accepted.active _ member) inputs.setup
    (by simpa only [actualInput, words.pc, Jump.initialPC, Control.initialPC] using retired_state_history past (Control.initialPC w).toBitVec)
    (retired_state_history native (Control.initialPC w).toBitVec) leftRange rightRange actualWords
    standardSource query actualEncoding aligned isa pcRead
  have retired := UnifiedReduced.Proofs.branch_register_retirement (by decide) core fields query
    (input := actualInput) actualEncoding 1 native spec
  refine ⟨before, after, past, current, future, ?_⟩
  simpa [JumpBranchSlt.Branch.execution, JumpBranchSlt.Branch.instruction, Reference.RiscV.Sail.registerClause, Option.get_some, actualInput, Trace.Row.start, Trace.Row.finish, Trace.Row.columns,
    CircuitLayout.columns, PCState.State.word, rawPair, importedConstraintsTraceColumns,
    Control.initialPC, Control.finalPC] using retired

theorem mixed_branch_cycle
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {initial : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    (accepted : MixedMemoryAccepted data program) (inputs : MixedMemoryInputs data program initial ca oa cells)
    (started : 0 < (timeOfPair data.machine.initial.timestamp).value)
    (isa : ∃ value, initial.regs.get? .misa = some value)
    {w : Nat → ZMod babyBearModulus} {input : Control.Branch.Input}
    (member : (⟨.machine, w⟩ : Trace.Row babyBearModulus UnifiedFamily) ∈ data.machine.rows)
    (words : Control.Branch.WordMapping input ⟨Control.destination w, Control.finalPC w⟩ w)
    (instruction : ∃ entry ∈ program, decoderQuery w = entry.query ∧
      entry.instruction = Control.Branch.instruction input ∧ entry.pc.toNat % 4 = 0) :
    ∃ events finalState,
      events.Perm (data.mixedSteps.map transferEvent) ∧
      SailHistory cells events initial finalState ∧
      RetiresCycle cells events initial finalState (⟨.machine, w⟩ : Trace.Row babyBearModulus UnifiedFamily)
        (JumpBranchSlt.Branch.execution input) := by
  have effects := mixed_memory_effects accepted inputs
  obtain ⟨events, finalState, permutation, order, history, _, _, _⟩ := effects.execution
  have retired := mixed_branch_cycle_at accepted inputs effects permutation order history isa member words instruction
  exact (fun _ : 0 < (timeOfPair data.machine.initial.timestamp).value =>
    ⟨events, finalState, permutation, history, retired⟩) started

theorem jump_fields {input : Jump.Input} {entry : UnifiedReduced.ProgramEntry}
    (fields : Mixed.decoderFields entry.instruction = some entry.data)
    (encoding : entry.instruction = Jump.instruction input) :
    UnifiedReduced.decoderFields entry.instruction = some entry.data := by
  rcases Mixed.Proofs.fields_cases fields with standard | custom
  · exact standard
  · rw [encoding] at custom
    cases kind : input.instruction <;> simp [Jump.instruction, JumpBranchSlt.Jump.instruction, kind, customDecoderFields] at custom

theorem mixed_jump_cycle_at
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {initial : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    (accepted : MixedMemoryAccepted data program) (inputs : MixedMemoryInputs data program initial ca oa cells)
    (effects : MixedMemoryEffects data initial cells)
    {events : List MemoryAccess} {finalState : State}
    (permutation : events.Perm (data.mixedSteps.map transferEvent))
    (order : events.Pairwise (fun a b => b.1 ≤ a.1))
    (history : SailHistory cells events initial finalState)
    (isa : ∃ value, initial.regs.get? .misa = some value)
    {w : Nat → ZMod babyBearModulus} {input : Jump.Input}
    (landingPad : input.instruction.indirect = true →
      initial.regs.get? .cur_privilege = some .Machine ∧
        ∃ security, initial.regs.get? .mseccfg = some security ∧
          SailRV32.Functions._get_Seccfg_MLPE security = 0)
    (member : (⟨.machine, w⟩ : Trace.Row babyBearModulus UnifiedFamily) ∈ data.machine.rows)
    (words : Jump.WordMapping input ⟨Control.destination w, Control.finalPC w⟩ w)
    (instruction : ∃ entry ∈ program, decoderQuery w = entry.query ∧
      entry.instruction = Jump.instruction input ∧ entry.pc.toNat % 4 = 0) :
      RetiresCycle cells events initial finalState (⟨.machine, w⟩ : Trace.Row babyBearModulus UnifiedFamily)
        (JumpBranchSlt.Jump.execution input) := by
  obtain ⟨entry, present, query, encoding, aligned⟩ := instruction
  have source := run_program_sources inputs.ordinaryProgram entry present
  have fields := jump_fields source.fields encoding
  have standardSource : entry.SourceWith initial UnifiedReduced.decoderFields := ⟨source.bytes, source.decoded, fields⟩
  have core := Verification.holds_of_sublist (accepted.constraints _ member)
    (List.sublist_append_left (importedConstraints data.machine.rom) importedConstraintsTimestampLookups)
  have metadata := UnifiedReduced.Proofs.jump_metadata encoding fields
  have ordinary : (⟨.machine, w⟩ : Trace.Row babyBearModulus UnifiedFamily) ∉ data.callers := by
    apply ordinary_of_decoder_mask (by decide) core fields query
    rw [metadata.1]
    split <;> split <;> decide
  obtain ⟨before, after, past, current, future, native, ranges⟩ :=
    ordinary_cycle_context_at accepted inputs effects permutation order history member ordinary
  have leftRange := ranges importedConstraintsMemoryPorts[0]
    (by simp [Trace.Row.ports, CircuitLayout.ports, importedConstraintsMemoryPorts])
  let actualInput : Jump.Input := {input with before := retiredState before (Control.initialPC w).toBitVec}
  have actualWords : Jump.WordMapping actualInput ⟨Control.destination w, Control.finalPC w⟩ w :=
    ⟨words.source, words.offset, words.pc, words.result, words.nextPC⟩
  have actualEncoding : entry.instruction = Jump.instruction actualInput := by
    simpa only [Jump.instruction, JumpBranchSlt.Jump.instruction, actualInput] using encoding
  have pcRead : run (SailRV32.Functions.get_arch_pc ()) actualInput.before =
      .ok actualInput.pc.toBitVec actualInput.before := by
    rw [show actualInput.pc = Control.initialPC w from words.pc]
    exact retired_state_pc before _
  have spec := Jump.Proofs.soundness_from_history (by decide) core inputs.setup
    (by simpa only [actualInput, words.pc, Jump.initialPC, Control.initialPC] using retired_state_history past (Control.initialPC w).toBitVec)
    (retired_state_history native (Control.initialPC w).toBitVec) leftRange actualWords
    standardSource query actualEncoding aligned isa landingPad pcRead
  have retired := UnifiedReduced.Proofs.jump_register_retirement (by decide) core fields query
    (input := actualInput) actualEncoding 1 native spec
  refine ⟨before, after, past, current, future, ?_⟩
  simpa [JumpBranchSlt.Jump.execution, JumpBranchSlt.Jump.instruction, Reference.RiscV.Sail.registerClause, Option.get_some, actualInput, Trace.Row.start, Trace.Row.finish, Trace.Row.columns,
    CircuitLayout.columns, PCState.State.word, rawPair, importedConstraintsTraceColumns,
    Control.initialPC, Control.finalPC] using retired

theorem mixed_jump_cycle
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {initial : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    (accepted : MixedMemoryAccepted data program) (inputs : MixedMemoryInputs data program initial ca oa cells)
    (started : 0 < (timeOfPair data.machine.initial.timestamp).value)
    (isa : ∃ value, initial.regs.get? .misa = some value)
    {w : Nat → ZMod babyBearModulus} {input : Jump.Input}
    (landingPad : input.instruction.indirect = true →
      initial.regs.get? .cur_privilege = some .Machine ∧
        ∃ security, initial.regs.get? .mseccfg = some security ∧
          SailRV32.Functions._get_Seccfg_MLPE security = 0)
    (member : (⟨.machine, w⟩ : Trace.Row babyBearModulus UnifiedFamily) ∈ data.machine.rows)
    (words : Jump.WordMapping input ⟨Control.destination w, Control.finalPC w⟩ w)
    (instruction : ∃ entry ∈ program, decoderQuery w = entry.query ∧
      entry.instruction = Jump.instruction input ∧ entry.pc.toNat % 4 = 0) :
    ∃ events finalState,
      events.Perm (data.mixedSteps.map transferEvent) ∧
      SailHistory cells events initial finalState ∧
      RetiresCycle cells events initial finalState (⟨.machine, w⟩ : Trace.Row babyBearModulus UnifiedFamily)
        (JumpBranchSlt.Jump.execution input) := by
  have effects := mixed_memory_effects accepted inputs
  obtain ⟨events, finalState, permutation, order, history, _, _, _⟩ := effects.execution
  have retired := mixed_jump_cycle_at accepted inputs effects permutation order history isa landingPad member words instruction
  exact (fun _ : 0 < (timeOfPair data.machine.initial.timestamp).value =>
    ⟨events, finalState, permutation, history, retired⟩) started

end Airbender.UnifiedReduced.Caller.Proofs
