import Slop.Keccak.PhysicalStep
import Slop.Delegation.ReverseFold

namespace Airbender.Keccak.Proofs
open Trace Trace.Proofs Delegation.Proofs Arithmetic Reference.RiscV.Sail
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000

theorem call_physical_steps [Fact p.Prime] (hp : 16777216 ≤ p)
    (inverse : 256 * (-7864320 : ZMod p) = 1)
    {data : Delegation.MemoryData p} {initial : State} {cells : List Cell}
    (accepted : Delegation.MemoryAccepted data) (inputs : BoundaryCallInputs data initial cells)
    (tables : data.setup = Delegation.modeledSetup Controller.rows)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    ∃ (pointer : BitVec 32) (after : State) (states : Fin 650 → LaneState),
      (Cell.register 11).read initial = .ok pointer initial ∧
      states 649 = physicalLanes initial pointer ∧ states 0 = physicalLanes after pointer ∧
      Delegation.TraceMapping data initial after cells ∧
      (∀ cell ∈ cells, ∃ value, cell.read after = .ok value after) ∧
      ∀ i : Fin 649, states ⟨i.val, by omega⟩ =
        microStep ⟨648 - i.val, by omega⟩ (states ⟨i.val + 1, by omega⟩) := by
  obtain ⟨pointer, ascending, count, after, boundaries, stateCount,
    pointerRead, permutation, head, last, trace, readable, effects⟩ :=
    call_state_trace hp inverse accepted inputs tables aligned
  obtain ⟨trackedPointer, trackedRead, tracked⟩ := call_state_cells hp inverse accepted inputs tables aligned
  have same : trackedPointer = pointer := by
    rw [pointerRead] at trackedRead
    exact (EStateM.Result.ok.inj trackedRead).1.symm
  subst trackedPointer
  obtain ⟨_, _, mapping, _⟩ := call_execution hp inverse accepted inputs tables aligned
  obtain ⟨mappedPointer, mappedRead, pointers, _⟩ := mapping
  have same : mappedPointer = pointer := by
    rw [pointerRead] at mappedRead
    exact (EStateM.Result.ok.inj mappedRead).1.symm
  subst mappedPointer
  have endpoints : boundaries[0]'(by omega) = after ∧ boundaries[649]'(by omega) = initial := by
    constructor
    · rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at head
      exact Option.some.inj head
    · have finish := List.getLast_of_getLast?_eq_some last
      simpa only [List.getLast_eq_getElem, stateCount] using finish
  let states : Fin 650 → LaneState := fun i => physicalLanes (boundaries[i.val]'(by omega)) pointer
  refine ⟨pointer, after, states, pointerRead, ?_, ?_, trace, ?_, ?_⟩
  · exact congrArg (fun state => physicalLanes state pointer) endpoints.2
  · exact congrArg (fun state => physicalLanes state pointer) endpoints.1
  · simpa only [endpoints.1] using readable 0 (by omega)
  · intro i
    let row := ascending.reverse[i.val]'(by simpa only [List.length_reverse, count] using i.isLt)
    have member : row ∈ data.rows :=
      ((List.reverse_perm ascending).trans permutation).mem_iff.mp (List.getElem_mem _)
    obtain ⟨events, eventPerm, history, effect, control, observed⟩ := effects i
    change events.Perm (row.memorySteps.map transferEvent) at eventPerm
    have eventPerm : events.Perm ((Delegation.Row.mk .keccak row.assignment).memorySteps.map transferEvent) := by
      simpa only [Delegation.Row.memorySteps, Delegation.Row.ports, Delegation.Row.writeToken,
        Delegation.Row.columns, inputs.family row member] using eventPerm
    exact native_physical_step ⟨648 - i.val, by omega⟩ effect (inputs.active row member)
      control (pointers row member) history eventPerm aligned tracked
      (readable (i.val + 1) (by omega)) observed

end Airbender.Keccak.Proofs
