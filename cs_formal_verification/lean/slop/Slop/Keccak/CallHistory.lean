import Slop.Keccak.CallExecution
import Slop.Delegation.CallHistory

namespace Airbender.Keccak.Proofs
open Trace Trace.Proofs Delegation.Proofs Arithmetic Reference.RiscV.Sail
set_option warningAsError true

theorem call_event_time (row : Delegation.Row p) {port : MemoryPort} (present : port ∈ row.ports) :
    (transferEvent (readToken row.assignment port, row.writeToken port)).1 = callWriteTime row + 1 := by
  have same : (row.writeToken port).time = (row.writeToken importedConstraintsMemoryPorts[0]).time := by
    change (_, _) = (_, _)
    rw [port_offset row present]
    rfl
  simp only [transferEvent, same, callWriteTime]

theorem call_scheduled_history [Fact p.Prime] (hp : 16777216 ≤ p)
    (inverse : 256 * (-7864320 : ZMod p) = 1)
    {data : Delegation.MemoryData p} {initial : State} {cells : List Cell}
    (accepted : Delegation.MemoryAccepted data) (inputs : BoundaryCallInputs data initial cells)
    (tables : data.setup = Delegation.modeledSetup Controller.rows)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    ∃ ascending : List (Delegation.Row p), ∃ count : ascending.length = 649, ∃ after : State,
      ascending.Perm data.rows ∧
      ascending.Pairwise (fun a b => callWriteTime a < callWriteTime b) ∧
      (∀ i : Fin 649,
        let w := (ascending[i.val]'(by have := i.isLt; omega)).assignment
        Word.mk (w Variables.controlReadLo).val (w Variables.controlReadHi).val =
          ⟨(scheduleControl ⟨i.val, by omega⟩).packed, 0⟩ ∧
        Word.mk (w Variables.controlWriteLo).val (w Variables.controlWriteHi).val =
          ⟨(scheduleControl ⟨i.val + 1, by have := i.isLt; omega⟩).packed, 0⟩) ∧
      GroupedSailHistory cells (fun row => row.memorySteps.map transferEvent) ascending.reverse initial after ∧
      ∀ token ∈ data.terminal, ∃ cell ∈ cells, cell.addressCode = token.address ∧
        cell.read after = .ok (memoryWord token.value) after := by
  obtain ⟨execution, schedule, _, _⟩ := call_execution hp inverse accepted inputs tables aligned
  obtain ⟨ascending, count, perm, increasing, controls⟩ := schedule
  obtain ⟨events, after, permutation, eventOrder, history, _, _, _, terminal⟩ := execution
  let ordered := ascending.reverse
  have orderedPerm : ordered.Perm data.rows := (List.reverse_perm ascending).trans perm
  have rowOrder : ordered.Pairwise (fun a b => callWriteTime b + 1 < callWriteTime a + 1) := by
    apply List.pairwise_reverse.mpr
    exact increasing.imp (by intro a b less; omega)
  have projection : events.Perm (ordered.flatMap fun row => row.memorySteps.map transferEvent) := by
    have rows := List.Perm.flatMap_right (fun row => row.memorySteps.map transferEvent) orderedPerm
    have pooled : data.rows.flatMap (fun row => row.memorySteps.map transferEvent) = data.steps.map transferEvent := by
      simp only [Delegation.MemoryData.steps, List.map_flatMap]
    exact permutation.trans (pooled ▸ rows).symm
  have times : ∀ row ∈ ordered, ∀ event ∈ row.memorySteps.map transferEvent,
      event.1 = callWriteTime row + 1 := by
    intro row _ event present
    obtain ⟨edge, included, rfl⟩ := List.mem_map.mp present
    obtain ⟨port, member, rfl⟩ := List.mem_map.mp included
    exact call_event_time row (by simpa using member)
  exact ⟨ascending, count, after, perm, increasing, controls,
    grouped_history (fun row => callWriteTime row + 1) _ rowOrder eventOrder projection times history,
    terminal⟩

theorem call_history [Fact p.Prime] (hp : 16777216 ≤ p)
    (inverse : 256 * (-7864320 : ZMod p) = 1)
    {data : Delegation.MemoryData p} {initial : State} {cells : List Cell}
    (accepted : Delegation.MemoryAccepted data) (inputs : BoundaryCallInputs data initial cells)
    (tables : data.setup = Delegation.modeledSetup Controller.rows)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    ∃ (ordered : List (Delegation.Row p)) (after : State), ordered.Perm data.rows ∧
      GroupedSailHistory cells (fun row => row.memorySteps.map transferEvent) ordered initial after ∧
      ∀ token ∈ data.terminal, ∃ cell ∈ cells, cell.addressCode = token.address ∧
        cell.read after = .ok (memoryWord token.value) after := by
  obtain ⟨ascending, _, after, perm, _, _, history, terminal⟩ :=
    call_scheduled_history hp inverse accepted inputs tables aligned
  exact ⟨ascending.reverse, after, (List.reverse_perm ascending).trans perm, history, terminal⟩

end Airbender.Keccak.Proofs
