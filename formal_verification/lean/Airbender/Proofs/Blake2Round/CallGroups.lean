import Airbender.Proofs.Blake2Round.CallExecution
import Airbender.Proofs.Delegation.CallHistory

namespace Airbender.Blake2Round.Proofs
open Trace Trace.Proofs Delegation.Proofs Reference.RiscV.Sail
set_option warningAsError true

theorem call_event_time (row : Delegation.Row p) {port : MemoryPort} (present : port ∈ row.ports) :
    (transferEvent (readToken row.assignment port, row.writeToken port)).1 =
      (timeOfPair (row.writeToken importedConstraintsMemoryPorts[42]).time).value + 1 := by
  have same : (row.writeToken port).time = (row.writeToken importedConstraintsMemoryPorts[42]).time := by
    change (_, _) = (_, _)
    rw [port_offset row present]
    rfl
  simp only [transferEvent, same]

theorem call_history [Fact p.Prime] (hp : 8388608 ≤ p)
    (inverse : 64 * (-31457280 : ZMod p) = 1)
    {data : Delegation.MemoryData p} {initial : State} {cells : List Cell} {flags : Fin 8}
    (accepted : Delegation.MemoryAccepted data) (inputs : CallInputs data initial cells flags)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    ∃ (ordered : List (Delegation.Row p)) (after : State), ordered.Perm data.rows ∧
      GroupedSailHistory cells (fun row => row.memorySteps.map transferEvent) ordered initial after ∧
      (∀ row ∈ data.rows, ∃ round, Memory.RoundMask row.assignment round ∧
        Row.spec (Native.input round row.assignment) (Native.output row.assignment)) ∧
      ∀ token ∈ data.terminal, ∃ cell ∈ cells, cell.addressCode = token.address ∧
        cell.read after = .ok (memoryWord token.value) after := by
  obtain ⟨_, execution, effects⟩ := call_execution hp inverse accepted inputs aligned
  have clockBound : 2 * timestampBase + 4 < p := by norm_num [timestampBase]; omega
  obtain ⟨ascending, perm, increasing⟩ := call_order clockBound accepted inputs
  obtain ⟨events, after, permutation, eventOrder, history, _, _, _, terminal⟩ := execution
  let ordered := ascending.reverse
  have orderedPerm : ordered.Perm data.rows := (List.reverse_perm ascending).trans perm
  let clock := fun row : Delegation.Row p =>
    (timeOfPair (row.writeToken importedConstraintsMemoryPorts[42]).time).value + 1
  have rowOrder : ordered.Pairwise (fun a b => clock b < clock a) := by
    apply List.pairwise_reverse.mpr
    exact increasing.imp (by intro a b less; change _ + 1 < _ + 1; omega)
  have projection : events.Perm (ordered.flatMap fun row => row.memorySteps.map transferEvent) := by
    have rows := List.Perm.flatMap_right (fun row => row.memorySteps.map transferEvent) orderedPerm
    have pooled : data.rows.flatMap (fun row => row.memorySteps.map transferEvent) = data.steps.map transferEvent := by
      simp only [Delegation.MemoryData.steps, List.map_flatMap]
    exact permutation.trans (pooled ▸ rows).symm
  have times : ∀ row ∈ ordered, ∀ event ∈ row.memorySteps.map transferEvent, event.1 = clock row := by
    intro row _ event present
    obtain ⟨edge, included, rfl⟩ := List.mem_map.mp present
    obtain ⟨port, member, rfl⟩ := List.mem_map.mp included
    exact call_event_time row (by simpa using member)
  exact ⟨ordered, after, orderedPerm,
    grouped_history clock _ rowOrder eventOrder projection times history, effects, terminal⟩

end Airbender.Blake2Round.Proofs
