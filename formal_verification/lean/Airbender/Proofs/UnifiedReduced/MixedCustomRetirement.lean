import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Proofs.UnifiedReduced.MixedRetirement
import Airbender.Proofs.UnifiedReduced.CustomComposition

namespace Airbender.UnifiedReduced.Caller.Proofs
open Arithmetic Reference.RiscV Reference.RiscV.Sail Reference.Sail Trace Trace.Proofs
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

theorem custom_fields_of_clause {instruction : SailRV32.instruction} {data : DecoderData UnifiedFamily}
    (fields : Mixed.decoderFields instruction = some data)
    (supported : Custom.clauseFor instruction ≠ none) : customDecoderFields instruction = some data := by
  rcases Mixed.Proofs.fields_cases fields with standard | custom
  · cases instruction with
    | ZIMOP_MOP_RR value | ZIMOP_MOP_R value =>
      simp [UnifiedReduced.decoderFields, Trace.decoderFields, JumpBranchSlt.decoderFields,
        ShiftBinop.decoderFields] at standard
    | _ => simp [Custom.clauseFor] at supported
  · exact custom

theorem custom_ordinary [Fact p.Prime] (hp : FieldCapacity.NoWrap p 524288)
    {data : RequestTrace p} {w : Nat → ZMod p} {entry : UnifiedReduced.ProgramEntry}
    (core : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints data.machine.rom))
    (fields : customDecoderFields entry.instruction = some entry.data) (query : decoderQuery w = entry.query) :
    (⟨.machine, w⟩ : Trace.Row p UnifiedFamily) ∉ data.callers := by
  have flag := UnifiedReduced.Proofs.decoder_selectors hp core
    (UnifiedReduced.Proofs.custom_field_bounds fields).2.1 query 7
  have disabled : w importedConstraintsDecoderColumns.flags[7] = 0 := by
    rcases UnifiedReduced.Proofs.custom_field_mask fields with mask | mask
    all_goals simpa [mask, Nat.testBit, Nat.shiftRight_eq_div_pow] using flag
  intro member
  have selected := of_decide_eq_true (List.mem_filter.mp member).2
  change w importedConstraintsDecoderColumns.flags[7] = 1 at selected
  exact zero_ne_one (disabled.symm.trans selected)

set_option backward.isDefEq.respectTransparency false in
theorem mixed_custom_cycle_at
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {initial : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    (accepted : MixedMemoryAccepted data program) (inputs : MixedMemoryInputs data program initial ca oa cells)
    (effects : MixedMemoryEffects data initial cells)
    {events : List MemoryAccess} {finalState : State}
    (permutation : events.Perm (data.mixedSteps.map transferEvent))
    (order : events.Pairwise (fun a b => b.1 ≤ a.1))
    (history : SailHistory cells events initial finalState)
    {w : Nat → ZMod babyBearModulus}
    (member : (⟨.machine, w⟩ : Trace.Row babyBearModulus UnifiedFamily) ∈ data.machine.rows)
    {entry : UnifiedReduced.ProgramEntry} (present : entry ∈ program)
    (query : decoderQuery w = entry.query) (supported : Custom.clauseFor entry.instruction ≠ none) :
    ∃ clause,
      Custom.clauseFor entry.instruction = some clause ∧
      RetiresCycle cells events initial finalState (⟨.machine, w⟩ : Trace.Row babyBearModulus UnifiedFamily) clause := by
  have source := run_program_sources inputs.ordinaryProgram entry present
  have fields := custom_fields_of_clause source.fields supported
  have core := Verification.holds_of_sublist (accepted.constraints _ member)
    (List.sublist_append_left (importedConstraints data.machine.rom) importedConstraintsTimestampLookups)
  have ordinary := custom_ordinary (by decide) core fields query
  obtain ⟨before, after, past, current, future, native, ranges⟩ :=
    ordinary_cycle_context_at accepted inputs effects permutation order history member ordinary
  have bounds (i : Fin 3) := ranges importedConstraintsMemoryPorts[i]
    (by fin_cases i <;> simp [Trace.Row.ports, CircuitLayout.ports, importedConstraintsMemoryPorts])
  have normalized := retired_state_history native (Control.initialPC w).toBitVec
  obtain arithmetic | rotation := UnifiedReduced.Proofs.custom_instruction_cases fields
  · obtain ⟨rs1, rs2, rd, encoding⟩ := arithmetic
    let input : TriAdd.Input := ⟨TriAdd.leftOperand w, TriAdd.rightOperand w, TriAdd.oldDestination w,
      rs1, rs2, rd, Control.initialPC w, retiredState before (Control.initialPC w).toBitVec⟩
    have words : TriAdd.WordMapping input ⟨Control.destination w, Control.finalPC w⟩ w := by
      constructor <;> rfl
    have spec := UnifiedReduced.Proofs.triadd_soundness_from_history (by decide) core (accepted.active _ member)
      normalized bounds words fields query encoding (retired_state_pc before _)
    have destination : (.Regidx entry.data.rd : SailRV32.regidx) = input.rd := by
      rw [(UnifiedReduced.Proofs.triadd_metadata fields (input := input) encoding).1]
    have retired := UnifiedReduced.Proofs.custom_register_retirement (by decide) core fields query destination 1 native spec
    refine ⟨TriAdd.execution input, ?_,
      before, after, past, current, future, ?_⟩
    · rw [encoding]; rfl
    · simpa [Trace.Row.start, Trace.Row.finish, Trace.Row.columns, CircuitLayout.columns,
        PCState.State.word, rawPair, importedConstraintsTraceColumns, Control.initialPC, Control.finalPC] using retired
  · obtain ⟨kind, rs1, rd, encoding⟩ := rotation
    let input : XorRotate.Input := ⟨kind, TriAdd.leftOperand w, TriAdd.rightOperand w,
      rs1, rd, Control.initialPC w, retiredState before (Control.initialPC w).toBitVec⟩
    have words : XorRotate.WordMapping input ⟨Control.destination w, Control.finalPC w⟩ w := by
      constructor <;> rfl
    have spec := UnifiedReduced.Proofs.xorrot_soundness_from_history (by decide) (by decide) core (accepted.active _ member)
      inputs.setup normalized words fields query encoding (retired_state_pc before _)
    have destination : (.Regidx entry.data.rd : SailRV32.regidx) = input.rd := by
      rw [(UnifiedReduced.Proofs.xorrot_metadata fields (input := input) encoding).1]
    have retired := UnifiedReduced.Proofs.custom_register_retirement (by decide) core fields query destination 1 native spec
    refine ⟨XorRotate.execution input, ?_,
      before, after, past, current, future, ?_⟩
    · rw [encoding]; fin_cases kind <;> rfl
    · simpa [Trace.Row.start, Trace.Row.finish, Trace.Row.columns, CircuitLayout.columns,
        PCState.State.word, rawPair, importedConstraintsTraceColumns, Control.initialPC, Control.finalPC] using retired

set_option backward.isDefEq.respectTransparency false in
theorem mixed_custom_cycle
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {initial : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    (accepted : MixedMemoryAccepted data program) (inputs : MixedMemoryInputs data program initial ca oa cells)
    (started : 0 < (timeOfPair data.machine.initial.timestamp).value)
    {w : Nat → ZMod babyBearModulus}
    (member : (⟨.machine, w⟩ : Trace.Row babyBearModulus UnifiedFamily) ∈ data.machine.rows)
    {entry : UnifiedReduced.ProgramEntry} (present : entry ∈ program)
    (query : decoderQuery w = entry.query) (supported : Custom.clauseFor entry.instruction ≠ none) :
    ∃ events finalState clause,
      Custom.clauseFor entry.instruction = some clause ∧
      events.Perm (data.mixedSteps.map transferEvent) ∧
      SailHistory cells events initial finalState ∧
      RetiresCycle cells events initial finalState (⟨.machine, w⟩ : Trace.Row babyBearModulus UnifiedFamily) clause := by
  have effects := mixed_memory_effects accepted inputs
  obtain ⟨events, finalState, permutation, order, history, _, _, _⟩ := effects.execution
  obtain ⟨clause, selected, retired⟩ :=
    mixed_custom_cycle_at accepted inputs effects permutation order history member present query supported
  exact (fun _ : 0 < (timeOfPair data.machine.initial.timestamp).value =>
    ⟨events, finalState, clause, selected, permutation, history, retired⟩) started

end Airbender.UnifiedReduced.Caller.Proofs
