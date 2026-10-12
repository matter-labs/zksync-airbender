import Airbender.Proofs.UnifiedReduced.MixedRetirement
import Airbender.Proofs.UnifiedReduced.BinaryExecution

namespace Airbender.UnifiedReduced.Caller.Proofs
open Arithmetic Reference.RiscV Reference.RiscV.Sail Reference.Sail Trace Trace.Proofs
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

theorem binary_fields {input : Binary.Input} {entry : UnifiedReduced.ProgramEntry} (shift : Bool)
    (fields : Mixed.decoderFields entry.instruction = some entry.data)
    (encoding : (if shift then Shift.instruction input else Binary.instruction input) = some entry.instruction) :
    UnifiedReduced.decoderFields entry.instruction = some entry.data := by
  rcases Mixed.Proofs.fields_cases fields with standard | custom
  · exact standard
  · rcases input with ⟨operation, immediate, left, right, pc, rs1, rs2, rd, encoded, before⟩
    cases shift <;> cases operation <;> cases immediate
    all_goals simp [Shift.instruction, Binary.instruction] at encoding
    all_goals rw [← encoding] at custom
    all_goals simp [customDecoderFields] at custom

theorem binary_ordinary [Fact p.Prime] (hp : 524288 < p)
    {data : RequestTrace p} {w : Nat → ZMod p} {input : Binary.Input} {entry : UnifiedReduced.ProgramEntry}
    (shift : Bool)
    (core : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints data.machine.rom))
    (fields : UnifiedReduced.decoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query)
    (encoding : (if shift then Shift.instruction input else Binary.instruction input) = some entry.instruction) :
    (⟨.machine, w⟩ : Trace.Row p UnifiedFamily) ∉ data.callers := by
  have metadata := UnifiedReduced.Proofs.binary_metadata shift encoding fields
  apply ordinary_of_decoder_mask hp core fields query
  rw [metadata.1]
  cases shift <;> decide

theorem mixed_binary_cycle
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {initial : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    (accepted : MixedMemoryAccepted data program) (inputs : MixedMemoryInputs data program initial ca oa cells)
    (started : 0 < (timeOfPair data.machine.initial.timestamp).value) (shift : Bool)
    {w : Nat → ZMod babyBearModulus} {input : Binary.Input}
    (member : (⟨.machine, w⟩ : Trace.Row babyBearModulus UnifiedFamily) ∈ data.machine.rows)
    (words : Binary.WordMapping input ⟨Control.destination w, Control.finalPC w⟩ w)
    (instruction : ∃ entry ∈ program, decoderQuery w = entry.query ∧
      (if shift then Shift.instruction input else Binary.instruction input) = some entry.instruction) :
    ∃ events finalState,
      events.Perm (data.mixedSteps.map transferEvent) ∧
      SailHistory cells events initial finalState ∧
      RetiresCycle cells events initial finalState (⟨.machine, w⟩ : Trace.Row babyBearModulus UnifiedFamily)
        (ShiftBinop.execution input) := by
  obtain ⟨entry, present, query, encoding⟩ := instruction
  have source := run_program_sources inputs.ordinaryProgram entry present
  have fields := binary_fields shift source.fields encoding
  have core := Verification.holds_of_sublist (accepted.constraints _ member)
    (List.sublist_append_left (importedConstraints data.machine.rom) importedConstraintsTimestampLookups)
  have ordinary := binary_ordinary (by decide) shift core fields query encoding
  obtain ⟨events, finalState, before, after, permutation, history, past, current, future, native, ranges⟩ :=
    ordinary_cycle_context accepted inputs started member ordinary
  have rightBound := ranges importedConstraintsMemoryPorts[1]
    (by simp [Trace.Row.ports, CircuitLayout.ports, importedConstraintsMemoryPorts])
  let actualInput : Binary.Input := {input with before := retiredState before (Control.initialPC w).toBitVec}
  have actualWords : Binary.WordMapping actualInput ⟨Control.destination w, Control.finalPC w⟩ w :=
    ⟨words.left, words.right, words.pc, words.result, words.nextPC⟩
  have normalized := retired_state_history native (Control.initialPC w).toBitVec
  have pcRead : run (SailRV32.Functions.get_arch_pc ()) actualInput.before =
      .ok actualInput.pc.toBitVec actualInput.before := by
    rw [show actualInput.pc = Control.initialPC w from words.pc]
    exact retired_state_pc before _
  have actualEncoding : (if shift then Shift.instruction actualInput else Binary.instruction actualInput) =
      some entry.instruction := by
    simpa only [Shift.instruction, Binary.instruction, actualInput] using encoding
  have spec : ShiftBinop.spec actualInput ⟨Control.destination w, Control.finalPC w⟩ := by
    cases choice : shift
    · exact Binary.Proofs.soundness_from_history (by decide) (by decide) core (accepted.active _ member)
        inputs.setup normalized rightBound actualWords fields query (by simpa [choice] using actualEncoding) pcRead
    · exact Shift.Proofs.soundness_from_history (by decide) (by decide) core (accepted.active _ member)
        inputs.setup normalized rightBound actualWords fields query (by simpa [choice] using actualEncoding) pcRead
  have retired := UnifiedReduced.Proofs.binary_register_retirement (by decide) shift core fields query
    (input := actualInput) actualEncoding 1 native spec
  refine ⟨events, finalState, permutation, history, before, after, past, current, future, ?_⟩
  simpa [ShiftBinop.execution, actualInput, Trace.Row.start, Trace.Row.finish, Trace.Row.columns,
    CircuitLayout.columns, PCState.State.word, rawPair, importedConstraintsTraceColumns,
    Control.initialPC, Control.finalPC] using retired

end Airbender.UnifiedReduced.Caller.Proofs
