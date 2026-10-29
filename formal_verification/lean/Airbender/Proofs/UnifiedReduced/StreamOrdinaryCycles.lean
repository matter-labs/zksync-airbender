import Airbender.Proofs.UnifiedReduced.StreamCycles
import Airbender.Proofs.UnifiedReduced.MixedCustomRetirement

namespace Airbender.UnifiedReduced.Caller.Stream.Proofs
open Arithmetic Reference.RiscV Reference.RiscV.Sail Reference.Sail Trace Trace.Proofs
open Caller.Proofs
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- Public custom metadata and native history derive TRIADD/XORROT retirement. -/
theorem custom_cycle_at
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {initial : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    (accepted : MixedMemoryAccepted data program) (inputs : NativeMemoryInputsWith Stream.decoderFields data program initial ca oa cells)
    (effects : MixedMemoryEffects data initial cells)
    {events : List MemoryAccess} {finalState : State}
    (permutation : events.Perm (data.mixedSteps.map transferEvent))
    (order : events.Pairwise (fun a b => b.1 ≤ a.1))
    (history : SailHistory cells events initial finalState)
    {w : Nat → ZMod babyBearModulus}
    (member : (⟨.machine, w⟩ : Trace.Row babyBearModulus UnifiedFamily) ∈ data.machine.rows)
    {entry : UnifiedReduced.ProgramEntry}
    (fields : customDecoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query) :
    ∃ clause,
      Custom.clauseFor entry.instruction = some clause ∧
      RetiresCycle cells events initial finalState (⟨.machine, w⟩ : Trace.Row babyBearModulus UnifiedFamily) clause := by
  have core := Verification.holds_of_sublist (accepted.constraints _ member)
    (List.sublist_append_left (importedConstraints data.machine.rom) importedConstraintsTimestampLookups)
  have ordinary := custom_ordinary (by decide) core fields query
  obtain ⟨before, after, past, current, future, native, ranges⟩ :=
    ordinary_context_at accepted inputs effects permutation order history member ordinary
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

/-- Public arithmetic metadata and native history derive ordinary retirement. -/
theorem arithmetic_cycle_at
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {initial : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    (accepted : MixedMemoryAccepted data program) (inputs : NativeMemoryInputsWith Stream.decoderFields data program initial ca oa cells)
    (effects : MixedMemoryEffects data initial cells)
    {events : List MemoryAccess} {finalState : State}
    (permutation : events.Perm (data.mixedSteps.map transferEvent))
    (order : events.Pairwise (fun a b => b.1 ≤ a.1))
    (history : SailHistory cells events initial finalState)
    {w : Nat → ZMod babyBearModulus} {input : Input}
    (member : (⟨.machine, w⟩ : Trace.Row babyBearModulus UnifiedFamily) ∈ data.machine.rows)
    (words : WordMapping input ⟨Control.destination w, Control.finalPC w⟩ w)
    (registers : ∀ index, input.rs1 = .Regidx index ∨ input.rs2 = .Regidx index → Cell.register index ∈ cells)
    {entry : UnifiedReduced.ProgramEntry}
    (fields : UnifiedReduced.decoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query)
    (encoding : entry.instruction = arithmeticInstruction input) :
      RetiresCycle cells events initial finalState (⟨.machine, w⟩ : Trace.Row babyBearModulus UnifiedFamily)
        (Sail.execution input) := by
  have core := Verification.holds_of_sublist (accepted.constraints _ member)
    (List.sublist_append_left (importedConstraints data.machine.rom) importedConstraintsTimestampLookups)
  have ordinary := arithmetic_ordinary (by decide) core fields encoding query
  obtain ⟨before, after, past, current, future, native, ranges⟩ :=
    ordinary_context_at accepted inputs effects permutation order history member ordinary
  have bounds : (readToken w importedConstraintsMemoryPorts[0]).word.Bounded ∧
      (readToken w importedConstraintsMemoryPorts[1]).word.Bounded := by
    constructor
    all_goals apply ranges
    all_goals simp [Trace.Row.ports, CircuitLayout.ports, importedConstraintsMemoryPorts]
  let actualInput : Input := { input with before := retiredState before (Control.initialPC w).toBitVec }
  have pcWord : input.row.pc = Control.initialPC w := congrArg₂ Word.mk words.pcLo words.pcHi
  have pc : run (SailRV32.Functions.get_arch_pc ()) actualInput.before =
      .ok actualInput.row.pc.toBitVec actualInput.before := by
    change run (SailRV32.Functions.get_arch_pc ()) (retiredState before (Control.initialPC w).toBitVec) = _
    rw [show actualInput.row.pc = Control.initialPC w from pcWord]
    exact retired_state_pc before _
  have actualWords : WordMapping actualInput ⟨Control.destination w, Control.finalPC w⟩ w :=
    ⟨words.leftLo, words.leftHi, words.rightLo, words.rightHi, words.immediateLo, words.immediateHi,
      words.pcLo, words.pcHi, words.destinationIndex, words.outputLo, words.outputHi,
      words.finalPCLo, words.finalPCHi⟩
  have spec := UnifiedReduced.Proofs.arithmetic_soundness_from_history (by decide) core (accepted.active _ member)
    (retired_state_image inputs.initialization (Control.initialPC w).toBitVec)
    (retired_state_history past (Control.initialPC w).toBitVec)
    (retired_state_history native (Control.initialPC w).toBitVec)
    (input := actualInput) registers bounds actualWords fields query encoding pc
  have retired := UnifiedReduced.Proofs.arithmetic_register_retirement (by decide) core fields query
    (input := actualInput) encoding 1 native spec
  refine ⟨before, after, past, current, future, ?_⟩
  simpa [Sail.execution, Sail.instruction, Reference.RiscV.Sail.registerClause, Option.get_some, actualInput, Trace.Row.start, Trace.Row.finish, Trace.Row.columns, CircuitLayout.columns,
    PCState.State.word, rawPair, importedConstraintsTraceColumns, Control.initialPC, Control.finalPC] using retired

end Airbender.UnifiedReduced.Caller.Stream.Proofs
