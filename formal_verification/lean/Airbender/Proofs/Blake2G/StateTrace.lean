import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Review.Helpers.Core.SerializedInverse
import Airbender.Proofs.Blake2G.CallGroups
import Airbender.Proofs.Blake2G.PointerHistory
import Airbender.Proofs.Delegation.CallBoundaries

namespace Airbender.Blake2G.Proofs
open Trace Trace.Proofs Delegation.Proofs Arithmetic Reference.RiscV.Sail
set_option warningAsError true
set_option maxRecDepth 16384

theorem call_state_trace [Fact p.Prime] (hp : FieldCapacity.NativeHashCapacity p)
    (inverse : SerializedInverse.Scale64 p)
    {data : Delegation.MemoryData p} {initial : State} {cells : List Cell} {reduced : Bool}
    (accepted : Delegation.MemoryAccepted data) (inputs : BoundaryCallInputs data initial cells reduced)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    ∃ (ascending : List (Delegation.Row p)), ∃ count : ascending.length = data.rows.length,
    ∃ (after : State) (states : List State), ∃ stateCount : states.length = data.rows.length + 1,
      ascending.Perm data.rows ∧ states.head? = some after ∧ states.getLast? = some initial ∧
      Delegation.TraceMapping data initial after cells ∧
      (∀ (i : Nat) (bound : i < states.length), ∀ cell ∈ cells,
        ∃ value, cell.read (states[i]'bound) = .ok value (states[i]'bound)) ∧
      ∀ i : Fin data.rows.length,
        let row := ascending.reverse[i.val]'(by simpa only [List.length_reverse, count] using i.isLt)
        Blake2G.spec (Native.input row.assignment) (Native.output row.assignment) ∧
        (readToken row.assignment importedConstraintsMemoryPorts[8]).word =
          controlAt reduced (data.rows.length - 1 - i.val) ∧
        ∃ events : List MemoryAccess, events.Perm (row.memorySteps.map transferEvent) ∧
          SailHistory cells events (states[i.val + 1]'(by omega)) (states[i.val]'(by omega)) ∧
          ∀ port ∈ row.ports, ∃ cell ∈ cells, cell.addressCode = port.address.code row.assignment ∧
            cell.read (states[i.val + 1]'(by omega)) =
              .ok (memoryWord (port.readCode row.assignment)) (states[i.val + 1]'(by omega)) ∧
            cell.read (states[i.val]'(by omega)) =
              .ok (memoryWord (port.writeCode row.assignment)) (states[i.val]'(by omega)) := by
  obtain ⟨ascending, after, permutation, _, controls, _, history, effects, terminal⟩ :=
    call_scheduled_history hp inverse accepted inputs aligned
  have count := permutation.length_eq
  have reversedPerm := (List.reverse_perm ascending).trans permutation
  have clockBound : 2 * timestampBase + 4 < p := by norm_num [timestampBase]; omega
  obtain ⟨states, stateCount, head, last, readable, ports⟩ :=
    grouped_atomic_boundaries clockBound accepted inputs.memory reversedPerm history aligned
  have stateLength : states.length = data.rows.length + 1 := by
    simpa only [List.length_reverse, count] using stateCount
  have trace := grouped_trace_mapping reversedPerm history terminal
  refine ⟨ascending, count, after, states, stateLength, permutation, head, last, trace, readable, ?_⟩
  intro i
  let row := ascending.reverse[i.val]'(by simpa only [List.length_reverse, count] using i.isLt)
  have member : row ∈ data.rows := reversedPerm.mem_iff.mp (List.getElem_mem _)
  have index : row = ascending[data.rows.length - 1 - i.val]'(by omega) := by
    simp only [row, List.getElem_reverse, count]
  have control := (controls (data.rows.length - 1 - i.val) (by omega)).1
  rw [← index] at control
  obtain ⟨events, eventPerm, current, observed⟩ :=
    ports i.val (by simpa only [List.length_reverse, count] using i.isLt)
  exact ⟨effects row member, control, events, eventPerm, current, observed⟩

end Airbender.Blake2G.Proofs
