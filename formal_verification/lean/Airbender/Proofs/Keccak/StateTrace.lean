import Airbender.Proofs.Keccak.StateCells
import Airbender.Review.Keccak.Permutation
import Airbender.Proofs.Delegation.CallBoundaries

namespace Airbender.Keccak.Proofs
open Trace Trace.Proofs Delegation.Proofs Arithmetic Reference.RiscV.Sail
set_option warningAsError true
set_option maxRecDepth 16384

theorem call_state_trace [Fact p.Prime] (hp : 16777216 ≤ p)
    (inverse : 256 * (-7864320 : ZMod p) = 1)
    {data : Delegation.MemoryData p} {initial : State} {cells : List Cell}
    (accepted : Delegation.MemoryAccepted data) (inputs : CallInputs data initial cells)
    (tables : data.setup = Delegation.modeledSetup Controller.rows)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    ∃ pointer : BitVec 32, ∃ ascending : List (Delegation.Row p), ∃ count : ascending.length = 649,
    ∃ after : State, ∃ states : List State, ∃ stateCount : states.length = 650,
      (Cell.register 11).read initial = .ok pointer initial ∧ ascending.Perm data.rows ∧
      states.head? = some after ∧ states.getLast? = some initial ∧
      Permutation.TraceMapping data initial after cells ∧
      (∀ (i : Nat) (bound : i < states.length), ∀ cell ∈ cells,
        ∃ value, cell.read (states[i]'bound) = .ok value (states[i]'bound)) ∧
      ∀ i : Fin 649,
        let row := (ascending.reverse[i.val]'(by simpa only [List.length_reverse, count] using i.isLt))
        ∃ events : List MemoryAccess, events.Perm (row.memorySteps.map transferEvent) ∧
          SailHistory cells events (states[i.val + 1]'(by omega)) (states[i.val]'(by omega)) ∧
          Native.RowEffects row.assignment ∧
          (row.assignment Variables.controlReadLo).val = (scheduleControl ⟨648 - i.val, by omega⟩).packed ∧
          ∀ lane : Fin 6,
            let physical := (Controller.rows (Fin.ofNat 4096
              ((scheduleControl ⟨648 - i.val, by omega⟩).packed + 2048)))[lane]
            let address := pointer + BitVec.ofNat 32 (8 * physical)
            Native.readLane row.assignment lane = ramLane (states[i.val + 1]'(by omega)) address ∧
              Native.writtenLane row.assignment lane = ramLane (states[i.val]'(by omega)) address := by
  obtain ⟨ascending, count, after, permutation, _, controls, history, terminal⟩ :=
    call_scheduled_history hp inverse accepted inputs tables aligned
  have reversedPerm := (List.reverse_perm ascending).trans permutation
  have clockBound : 2 * timestampBase + 4 < p := by norm_num [timestampBase]; omega
  obtain ⟨states, stateCount, head, last, readable, ports⟩ :=
    grouped_atomic_boundaries clockBound accepted inputs.memory reversedPerm history aligned
  have stateLength : states.length = 650 := by simpa only [List.length_reverse, count] using stateCount
  obtain ⟨_, _, pointer, effects⟩ := call_execution hp inverse accepted inputs tables aligned
  obtain ⟨pointer, pointerRead, pointers, _⟩ := pointer
  have memory : Memory.Inputs data initial cells Controller.rows :=
    ⟨inputs.memory, inputs.family, by simp [tables, Delegation.modeledSetup], inputs.active⟩
  have bounds := Memory.Proofs.value_bounds clockBound accepted memory
  have trace : Permutation.TraceMapping data initial after cells := by
    obtain ⟨events, eventPerm, actual⟩ := ungrouped_history history
    have rowPerm := List.Perm.flatMap_right (fun row : Delegation.Row p => row.memorySteps.map transferEvent) reversedPerm
    have pooled : data.rows.flatMap (fun row => row.memorySteps.map transferEvent) = data.steps.map transferEvent := by
      simp only [Delegation.MemoryData.steps, List.map_flatMap]
    refine ⟨⟨events, pooled ▸ eventPerm.trans rowPerm, actual⟩, ?_⟩
    simpa only [Trace.MemoryToken.word, memoryWord] using terminal
  refine ⟨pointer, ascending, count, after, states, stateLength, pointerRead, permutation, head, last, trace, readable, ?_⟩
  intro i
  let row := ascending.reverse[i.val]'(by simpa only [List.length_reverse, count] using i.isLt)
  have member : row ∈ data.rows := reversedPerm.mem_iff.mp (List.getElem_mem _)
  have index : row = ascending[648 - i.val]'(by omega) := by
    simp only [row, List.getElem_reverse, count]
  have control : (row.assignment Variables.controlReadLo).val = (scheduleControl ⟨648 - i.val, by omega⟩).packed := by
    have control := congrArg Word.lo (controls ⟨648 - i.val, by omega⟩).1
    simpa only [← index] using control
  obtain ⟨events, eventsPerm, current, observed⟩ := ports i.val (by simpa only [List.length_reverse, count] using i.isLt)
  refine ⟨events, eventsPerm, current, effects row member, control, ?_⟩
  intro lane
  have native : row = ⟨.keccak, row.assignment⟩ := by
    have native : row = ⟨row.family, row.assignment⟩ := rfl
    simpa only [inputs.family row member] using native
  have reads : ∀ port ∈ (⟨.keccak, row.assignment⟩ : Delegation.Row p).ports,
      (readToken row.assignment port).word.Bounded := by
    simpa only [← native] using bounds.1 row member
  have writes : ∀ port ∈ (⟨.keccak, row.assignment⟩ : Delegation.Row p).ports,
      ((⟨.keccak, row.assignment⟩ : Delegation.Row p).writeToken port).word.Bounded := by
    simpa only [← native] using bounds.2.1 row member
  have actual : ∀ port ∈ (⟨.keccak, row.assignment⟩ : Delegation.Row p).ports,
      ∃ cell : Cell, cell.addressCode = port.address.code row.assignment ∧
        cell.read (states[i.val + 1]'(by omega)) =
          .ok (memoryWord (port.readCode row.assignment)) (states[i.val + 1]'(by omega)) ∧
        cell.read (states[i.val]'(by omega)) =
          .ok (memoryWord (port.writeCode row.assignment)) (states[i.val]'(by omega)) := by
    intro port present
    obtain ⟨cell, _, code, read, written⟩ := observed port (by simpa only [← native] using present)
    exact ⟨cell, code, read, written⟩
  have result := native_lane_observations (effects row member).addresses reads writes actual lane
  have physical := scheduled_lane_indices ⟨648 - i.val, by omega⟩ (effects row member)
    (inputs.active row member) control lane
  rw [pointers row member, Word.ofBitVec_roundtrip, physical] at result
  exact result

end Airbender.Keccak.Proofs
