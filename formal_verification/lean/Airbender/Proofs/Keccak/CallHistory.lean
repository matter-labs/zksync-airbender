import Airbender.Proofs.Keccak.CallExecution
import Airbender.Proofs.Delegation.CallHistory

namespace Airbender.Keccak.Proofs
open Trace Trace.Proofs Delegation.Proofs Reference.RiscV.Sail
set_option warningAsError true

theorem call_event_time (row : Delegation.Row p) {port : MemoryPort} (present : port ∈ row.ports) :
    (transferEvent (readToken row.assignment port, row.writeToken port)).1 = callWriteTime row + 1 := by
  have same : (row.writeToken port).time = (row.writeToken importedConstraintsMemoryPorts[0]).time := by
    change (_, _) = (_, _)
    rw [port_offset row present]
    rfl
  simp only [transferEvent, same, callWriteTime]

theorem call_history [Fact p.Prime] (hp : 16777216 ≤ p)
    (inverse : 256 * (-7864320 : ZMod p) = 1)
    {data : Delegation.MemoryData p} {initial : State} {cells : List Cell}
    (accepted : Delegation.MemoryAccepted data) (inputs : CallInputs data initial cells)
    (tables : data.setup = Delegation.modeledSetup Controller.rows)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    ∃ (ordered : List (Delegation.Row p)) (after : State), ordered.Perm data.rows ∧
      GroupedSailHistory cells (fun row => row.memorySteps.map transferEvent) ordered initial after ∧
      ∀ token ∈ data.terminal, ∃ cell ∈ cells, cell.addressCode = token.address ∧
        cell.read after = .ok (memoryWord token.value) after := by
  obtain ⟨execution, schedule, _, _⟩ := call_execution hp inverse accepted inputs tables aligned
  obtain ⟨ascending, count, perm, increasing, _⟩ := schedule
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
  exact ⟨ordered, after, orderedPerm,
    grouped_history (fun row => callWriteTime row + 1) _ rowOrder eventOrder projection times history,
    terminal⟩

end Airbender.Keccak.Proofs
