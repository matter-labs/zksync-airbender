import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Proofs.UnifiedReduced.MixedRetirement
import Airbender.Proofs.UnifiedReduced.ControlExecution

namespace Airbender.UnifiedReduced.Caller.Proofs
open Arithmetic Reference.RiscV Reference.RiscV.Sail Reference.Sail Trace Trace.Proofs
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

theorem comparison_fields {input : Control.Comparison.Input} {entry : UnifiedReduced.ProgramEntry}
    (fields : Mixed.decoderFields entry.instruction = some entry.data)
    (encoding : entry.instruction = Control.Comparison.instruction input) :
    UnifiedReduced.decoderFields entry.instruction = some entry.data := by
  rcases Mixed.Proofs.fields_cases fields with standard | custom
  · exact standard
  · rw [encoding] at custom
    cases operation : input.opcode <;> simp [Control.Comparison.instruction, JumpBranchSlt.Comparison.instruction, customDecoderFields, operation] at custom

theorem comparison_ordinary [Fact p.Prime] (hp : FieldCapacity.NoWrap p 524288)
    {data : RequestTrace p} {w : Nat → ZMod p} {input : Control.Comparison.Input} {entry : UnifiedReduced.ProgramEntry}
    (core : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints data.machine.rom))
    (fields : UnifiedReduced.decoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query)
    (encoding : entry.instruction = Control.Comparison.instruction input) :
    (⟨.machine, w⟩ : Trace.Row p UnifiedFamily) ∉ data.callers := by
  have metadata := UnifiedReduced.Proofs.comparison_metadata encoding fields
  apply ordinary_of_decoder_mask hp core fields query
  rw [metadata.1]
  decide

theorem mixed_comparison_cycle_at
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {initial : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    (accepted : MixedMemoryAccepted data program) (inputs : MixedMemoryInputs data program initial ca oa cells)
    (effects : MixedMemoryEffects data initial cells)
    {events : List MemoryAccess} {finalState : State}
    (permutation : events.Perm (data.mixedSteps.map transferEvent))
    (order : events.Pairwise (fun a b => b.1 ≤ a.1))
    (history : SailHistory cells events initial finalState)
    {w : Nat → ZMod babyBearModulus} {input : Control.Comparison.Input}
    (member : (⟨.machine, w⟩ : Trace.Row babyBearModulus UnifiedFamily) ∈ data.machine.rows)
    (words : Control.Comparison.WordMapping input ⟨Control.destination w, Control.finalPC w⟩ w)
    (instruction : ∃ entry ∈ program, decoderQuery w = entry.query ∧
      entry.instruction = Control.Comparison.instruction input ∧ entry.pc.toNat % 4 = 0) :
      RetiresCycle cells events initial finalState (⟨.machine, w⟩ : Trace.Row babyBearModulus UnifiedFamily)
        (JumpBranchSlt.Comparison.execution input) := by
  obtain ⟨entry, present, query, encoding, aligned⟩ := instruction
  have source := run_program_sources inputs.ordinaryProgram entry present
  have fields := comparison_fields source.fields encoding
  have core := Verification.holds_of_sublist (accepted.constraints _ member)
    (List.sublist_append_left (importedConstraints data.machine.rom) importedConstraintsTimestampLookups)
  have ordinary := comparison_ordinary (by decide) core fields query encoding
  obtain ⟨before, after, past, current, future, native, ranges⟩ :=
    ordinary_cycle_context_at accepted inputs effects permutation order history member ordinary
  have bounds : (readToken w importedConstraintsMemoryPorts[0]).word.Bounded ∧
      (readToken w importedConstraintsMemoryPorts[1]).word.Bounded := by
    constructor
    all_goals apply ranges
    all_goals simp [Trace.Row.ports, CircuitLayout.ports, importedConstraintsMemoryPorts]
  let actualInput : Control.Comparison.Input := {input with before := retiredState before (Control.initialPC w).toBitVec}
  have actualWords : Control.Comparison.WordMapping actualInput ⟨Control.destination w, Control.finalPC w⟩ w :=
    ⟨words.left, words.right, words.pc, words.result, words.nextPC⟩
  have normalized := retired_state_history native (Control.initialPC w).toBitVec
  have pcRead : run (SailRV32.Functions.get_arch_pc ()) actualInput.before =
      .ok actualInput.pc.toBitVec actualInput.before := by
    rw [show actualInput.pc = Control.initialPC w from words.pc]
    exact retired_state_pc before _
  have actualEncoding : entry.instruction = Control.Comparison.instruction actualInput := by
    simpa only [Control.Comparison.instruction, JumpBranchSlt.Comparison.instruction, actualInput] using encoding
  have spec := Control.Comparison.Proofs.soundness_from_history (by decide) core (accepted.active _ member)
    inputs.setup normalized bounds.1 bounds.2 actualWords fields query actualEncoding aligned pcRead
  have retired := UnifiedReduced.Proofs.comparison_register_retirement (by decide) core fields query
    (input := actualInput) actualEncoding 1 native spec
  refine ⟨before, after, past, current, future, ?_⟩
  simpa [JumpBranchSlt.Comparison.execution, JumpBranchSlt.Comparison.instruction, Reference.RiscV.Sail.registerClause, Option.get_some, actualInput, Trace.Row.start, Trace.Row.finish, Trace.Row.columns,
    CircuitLayout.columns, PCState.State.word, rawPair, importedConstraintsTraceColumns,
    Control.initialPC, Control.finalPC] using retired

theorem mixed_comparison_cycle
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {initial : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    (accepted : MixedMemoryAccepted data program) (inputs : MixedMemoryInputs data program initial ca oa cells)
    (started : 0 < (timeOfPair data.machine.initial.timestamp).value)
    {w : Nat → ZMod babyBearModulus} {input : Control.Comparison.Input}
    (member : (⟨.machine, w⟩ : Trace.Row babyBearModulus UnifiedFamily) ∈ data.machine.rows)
    (words : Control.Comparison.WordMapping input ⟨Control.destination w, Control.finalPC w⟩ w)
    (instruction : ∃ entry ∈ program, decoderQuery w = entry.query ∧
      entry.instruction = Control.Comparison.instruction input ∧ entry.pc.toNat % 4 = 0) :
    ∃ events finalState,
      events.Perm (data.mixedSteps.map transferEvent) ∧
      SailHistory cells events initial finalState ∧
      RetiresCycle cells events initial finalState (⟨.machine, w⟩ : Trace.Row babyBearModulus UnifiedFamily)
        (JumpBranchSlt.Comparison.execution input) := by
  have effects := mixed_memory_effects accepted inputs
  obtain ⟨events, finalState, permutation, order, history, _, _, _⟩ := effects.execution
  have retired := mixed_comparison_cycle_at accepted inputs effects permutation order history member words instruction
  exact (fun _ : 0 < (timeOfPair data.machine.initial.timestamp).value =>
    ⟨events, finalState, permutation, history, retired⟩) started

end Airbender.UnifiedReduced.Caller.Proofs
