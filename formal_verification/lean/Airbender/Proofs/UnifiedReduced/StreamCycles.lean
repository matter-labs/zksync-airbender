import Airbender.Proofs.UnifiedReduced.StreamMemory
import Airbender.Proofs.UnifiedReduced.ExternalInput
import Airbender.Proofs.UnifiedReduced.ModularNative
import Airbender.Proofs.UnifiedReduced.MixedRetirement

namespace Airbender.UnifiedReduced.Caller.Stream.Proofs
open Arithmetic Trace Trace.Proofs Reference.RiscV.Sail Reference.Sail
open Caller.Proofs
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

/-- Exact native cycle states and read bounds do not depend on the registry. -/
theorem ordinary_context_at
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {initial : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    (accepted : MixedMemoryAccepted data program)
    (inputs : NativeMemoryInputsWith Stream.decoderFields data program initial ca oa cells)
    (effects : MixedMemoryEffects data initial cells)
    {events : List MemoryAccess} {finalState : State}
    (permutation : events.Perm (data.mixedSteps.map transferEvent))
    (order : events.Pairwise (fun a b => b.1 ≤ a.1))
    (history : SailHistory cells events initial finalState)
    {row : Trace.Row babyBearModulus UnifiedFamily}
    (member : row ∈ data.machine.rows) (ordinary : row ∉ data.callers) :
    ∃ before after,
      SailHistory cells (events.filter fun event => decide
        (event.1 ≤ Delegation.Caller.startClock row)) initial before ∧
      SailHistory cells (events.filter fun event => decide
        (Delegation.Caller.startClock row < event.1 ∧
          event.1 ≤ Delegation.Caller.finishClock row)) before after ∧
      SailHistory cells (events.filter fun event => decide
        (Delegation.Caller.finishClock row < event.1)) after finalState ∧
      SailHistory cells (rowEvents 1 row).reverse before after ∧
      ∀ port ∈ row.ports, (readToken row.assignment port).word.Bounded := by
  have floor := machine_native_clock_positive (by decide) (by decide) accepted
    inputs.publicProgram inputs.initialization member
  have clocks := machine_clock_facts (by decide) (by decide)
    accepted.toRequestChecks inputs.publicProgram member
  obtain ⟨before, after, _, past, current, future⟩ := history_window order history
    (by omega : Delegation.Caller.startClock row ≤ Delegation.Caller.finishClock row)
  have cycle := cycle_window_permutation (by decide) (by decide)
    accepted.toRequestChecks inputs.publicProgram effects.requests permutation member (by omega)
  have native := ordinary_cycle_history (by decide) (by decide)
    accepted.toRequestChecks inputs.publicProgram member ordinary cycle
    (order.sublist List.filter_sublist) current
  refine ⟨before, after, past, current, future, native, ?_⟩
  intro port present
  exact (effects.words _ (mixed_machine_member member
    (by rwa [machine_ports_ordinary member ordinary]))).1

/-- Each external instruction retires inside its actual shared-memory cycle. -/
theorem external_cycle_at [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {initial : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    (accepted : MixedMemoryAccepted data program)
    (inputs : NativeMemoryInputsWith Stream.decoderFields data program initial ca oa cells)
    (effects : MixedMemoryEffects data initial cells)
    {events : List MemoryAccess} {finalState : State}
    (permutation : events.Perm (data.mixedSteps.map transferEvent))
    (order : events.Pairwise (fun a b => b.1 ≤ a.1))
    (history : SailHistory cells events initial finalState)
    {w : Nat → ZMod babyBearModulus}
    (member : (⟨.machine, w⟩ : Trace.Row babyBearModulus UnifiedFamily) ∈ data.machine.rows)
    (ordinary : (⟨.machine, w⟩ : Trace.Row babyBearModulus UnifiedFamily) ∉ data.callers)
    {entry : UnifiedReduced.ProgramEntry}
    (fields : Stream.externalDecoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query) (stream : List (BitVec 32)) (position : Nat)
    (port : Stream.isRead (⟨.machine, w⟩ : Trace.Row babyBearModulus UnifiedFamily) = true →
      stream[position]? = some (Control.destination w).toBitVec) :
    ∃ clause next,
      Stream.externalClause stream position entry.instruction = some (clause, next) ∧
      next = position + (if Stream.isRead
        (⟨.machine, w⟩ : Trace.Row babyBearModulus UnifiedFamily) then 1 else 0) ∧
      RetiresCycle cells events initial finalState
        (⟨.machine, w⟩ : Trace.Row babyBearModulus UnifiedFamily) clause := by
  have core := Verification.holds_of_sublist (accepted.constraints _ member)
    (List.sublist_append_left (importedConstraints data.machine.rom)
      importedConstraintsTimestampLookups)
  obtain ⟨before, after, past, current, future, native, _⟩ :=
    ordinary_context_at accepted inputs effects permutation order history member ordinary
  rcases external_fields_cases fields with ⟨rd, nonzero, encoding, metadata⟩ |
      ⟨rs1, nonzero, encoding, metadata⟩
  · change rd ≠ 0#5 at nonzero
    have flag := UnifiedReduced.Proofs.decoder_selectors (by decide) core
      (show entry.data.mask < 524288 by rw [metadata]; change 256 < 524288; decide +kernel) query 8
    have selected : Stream.isRead
        (⟨.machine, w⟩ : Trace.Row babyBearModulus UnifiedFamily) = true := by
      simp [metadata, importedConstraintsDecoderColumns, Nat.testBit,
        Nat.shiftRight_eq_div_pow] at flag
      simp [Stream.isRead, importedConstraintsDecoderColumns, flag]
    have supplied := port selected
    let clause := writeResult (.Regidx rd) (Word.ofBitVec (Control.destination w).toBitVec)
    refine ⟨clause, position + 1, ?_, by simp [selected],
      before, after, past, current, future, ?_⟩
    · simp [Stream.externalClause, encoding, NonDeterminism.clause, nonzero, supplied, clause]
    · have checked := ExternalInput.Proofs.read_execution (by decide) core
        (accepted.active _ member) metadata query stream position supplied 1 native
      change run (normalStep clause) (retiredState before (Control.initialPC w).toBitVec) =
        .ok SailRV32.Functions.RETIRE_SUCCESS
          (retiredState after (Control.finalPC w).toBitVec)
      simpa only [clause, writeResult, Word.ofBitVec_roundtrip] using checked
  · change rs1 ≠ 0#5 at nonzero
    have flag := UnifiedReduced.Proofs.decoder_selectors (by decide) core
      (show entry.data.mask < 524288 by rw [metadata]; change 1 < 524288; decide +kernel) query 8
    have selected : Stream.isRead
        (⟨.machine, w⟩ : Trace.Row babyBearModulus UnifiedFamily) = false := by
      simp [metadata, importedConstraintsDecoderColumns, Nat.testBit,
        Nat.shiftRight_eq_div_pow] at flag
      simp [Stream.isRead, importedConstraintsDecoderColumns, flag]
    refine ⟨pure SailRV32.Functions.RETIRE_SUCCESS, position, ?_, by simp [selected],
      before, after, past, current, future, ?_⟩
    · simp [Stream.externalClause, encoding, NonDeterminism.clause, nonzero]
    · exact ExternalInput.Proofs.hint_execution (by decide) core
        (accepted.active _ member) metadata query 1 native

/-- Every modular instruction uses its native values in the same cycle history. -/
theorem modular_cycle_at
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {initial : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    (accepted : MixedMemoryAccepted data program)
    (inputs : NativeMemoryInputsWith Stream.decoderFields data program initial ca oa cells)
    (registers : ∀ index, Cell.register index ∈ cells)
    (effects : MixedMemoryEffects data initial cells)
    {events : List MemoryAccess} {finalState : State}
    (permutation : events.Perm (data.mixedSteps.map transferEvent))
    (order : events.Pairwise (fun a b => b.1 ≤ a.1))
    (history : SailHistory cells events initial finalState)
    {w : Nat → ZMod babyBearModulus}
    (member : (⟨.machine, w⟩ : Trace.Row babyBearModulus UnifiedFamily) ∈ data.machine.rows)
    (ordinary : (⟨.machine, w⟩ : Trace.Row babyBearModulus UnifiedFamily) ∉ data.callers)
    {entry : UnifiedReduced.ProgramEntry}
    (fields : Modular.mopDecoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query) :
    ∃ clause, Modular.mopClause entry.instruction = some clause ∧
      RetiresCycle cells events initial finalState
        (⟨.machine, w⟩ : Trace.Row babyBearModulus UnifiedFamily) clause := by
  have core := Verification.holds_of_sublist (accepted.constraints _ member)
    (List.sublist_append_left (importedConstraints data.machine.rom)
      importedConstraintsTimestampLookups)
  obtain ⟨before, after, past, current, future, native, ranges⟩ :=
    ordinary_context_at accepted inputs effects permutation order history member ordinary
  have bounds (i : Fin 3) := ranges importedConstraintsMemoryPorts[i]
    (by fin_cases i <;> simp [Trace.Row.ports, CircuitLayout.ports, importedConstraintsMemoryPorts])
  obtain ⟨opcode, rs1, rs2, rd, encoding, _⟩ := Modular.Proofs.mop_cases fields
  refine ⟨AddSub.Modular.clause opcode rs1 rs2 rd, ?_,
    before, after, past, current, future, ?_⟩
  · rw [encoding]
    cases opcode <;> rfl
  · exact Modular.Proofs.execution_from_history inputs.initialization registers core
      (accepted.active _ member) bounds fields query opcode rs1 rs2 rd encoding 1 past native

end Airbender.UnifiedReduced.Caller.Stream.Proofs
