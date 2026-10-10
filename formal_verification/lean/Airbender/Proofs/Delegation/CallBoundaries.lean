import Airbender.Proofs.Delegation.CallHistory
import Airbender.Proofs.Delegation.AtomicHistory

namespace Airbender.Delegation.Proofs
open Trace Trace.Proofs Reference.RiscV.Sail
set_option warningAsError true

theorem grouped_boundaries {rows : List α} {cells : List Cell} {before after : State}
    {accesses : α → List MemoryAccess}
    (history : GroupedSailHistory cells accesses rows before after) :
    ∃ states : List State, ∃ count : states.length = rows.length + 1,
      states.head? = some after ∧ states.getLast? = some before ∧
      ∀ (i : Nat) (bound : i < rows.length), ∃ events : List MemoryAccess,
        events.Perm (accesses (rows[i]'bound)) ∧
          SailHistory cells events
            (states[i + 1]'(by omega)) (states[i]'(by omega)) := by
  induction history with
  | nil before =>
    refine ⟨[before], rfl, rfl, rfl, ?_⟩
    intro i bound
    simp at bound
  | @cons row rest before middle after events past permutation current ih =>
    obtain ⟨states, count, head, last, steps⟩ := ih
    refine ⟨after :: states, by simp only [List.length_cons]; omega, rfl, ?_, ?_⟩
    · simp only [List.getLast?_cons, last, Option.getD_some]
    · intro i bound
      cases i with
      | zero =>
        have first : states[0]'(by omega) = middle := by
          have first := head
          rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at first
          exact Option.some.inj first
        refine ⟨events, permutation, ?_⟩
        simpa only [List.getElem_cons_zero, List.getElem_cons_succ, first] using current
      | succ i =>
        have earlier : i < rest.length := by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using bound
        obtain ⟨earlierEvents, matching, realized⟩ := steps i earlier
        exact ⟨earlierEvents, matching, realized⟩

private theorem boundary_reads {rows : List α} {cells : List Cell} {initial : State}
    {accesses : α → List MemoryAccess} {states : List State}
    (count : states.length = rows.length + 1) (last : states.getLast? = some initial)
    (steps : ∀ (i : Nat) (bound : i < rows.length), ∃ events : List MemoryAccess,
      events.Perm (accesses (rows[i]'bound)) ∧
        SailHistory cells events (states[i + 1]'(by omega)) (states[i]'(by omega)))
    (aligned : ∀ cell ∈ cells, cell.Aligned)
    (noZero : ∀ row ∈ rows, ∀ event ∈ accesses row, event.2.1 ≠ (Cell.register 0).addressCode)
    (readable : ∀ cell ∈ cells, ∃ value, cell.read initial = .ok value initial) :
    ∀ (i : Nat) (bound : i < states.length), ∀ cell ∈ cells,
      ∃ value, cell.read (states[i]'bound) = .ok value (states[i]'bound) := by
  have establish : ∀ (n : Nat) (bound : n ≤ rows.length), ∀ cell ∈ cells,
      ∃ value, cell.read (states[rows.length - n]'(by omega)) =
        .ok value (states[rows.length - n]'(by omega)) := by
    intro n
    induction n with
    | zero =>
      intro bound
      have endpoint := List.getLast_of_getLast?_eq_some last
      have endpoint : states[rows.length]'(by omega) = initial := by
        simpa only [List.getLast_eq_getElem, count, Nat.add_sub_cancel] using endpoint
      simpa only [Nat.sub_zero, endpoint] using readable
    | succ n ih =>
      intro bound
      have indexBound : rows.length - (n + 1) < rows.length := by omega
      obtain ⟨events, permutation, current⟩ := steps (rows.length - (n + 1)) indexBound
      have earlier := ih (by omega)
      have previous : rows.length - (n + 1) + 1 = rows.length - n := by omega
      have current : SailHistory cells events (states[rows.length - n]'(by omega))
          (states[rows.length - (n + 1)]'(by omega)) := by
        simpa only [previous] using current
      exact history_readable current aligned (by
        intro event present
        exact noZero _ (List.getElem_mem _) event (permutation.mem_iff.mp present)) earlier
  intro i bound
  have result := establish (rows.length - i) (by omega)
  have index : rows.length - (rows.length - i) = i := by omega
  simpa only [index] using result

theorem grouped_atomic_boundaries [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {data : MemoryData p} (accepted : MemoryAccepted data)
    {initial after : State} {cells : List Cell} (inputs : MemoryInputs data initial cells)
    {ordered : List (Row p)} (permutation : ordered.Perm data.rows)
    (history : GroupedSailHistory cells (fun row => row.memorySteps.map transferEvent) ordered initial after)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    ∃ states : List State, ∃ count : states.length = ordered.length + 1,
      states.head? = some after ∧ states.getLast? = some initial ∧
      (∀ (i : Nat) (bound : i < states.length), ∀ cell ∈ cells,
        ∃ value, cell.read (states[i]'bound) = .ok value (states[i]'bound)) ∧
      ∀ (i : Nat) (bound : i < ordered.length),
        let row := ordered[i]'bound
        ∃ events : List MemoryAccess, events.Perm (row.memorySteps.map transferEvent) ∧
          SailHistory cells events (states[i + 1]'(by omega)) (states[i]'(by omega)) ∧
          ∀ port ∈ row.ports, ∃ cell ∈ cells, cell.addressCode = port.address.code row.assignment ∧
            cell.read (states[i + 1]'(by omega)) =
              .ok (memoryWord (port.readCode row.assignment)) (states[i + 1]'(by omega)) ∧
            cell.read (states[i]'(by omega)) =
              .ok (memoryWord (port.writeCode row.assignment)) (states[i]'(by omega)) := by
  obtain ⟨states, count, head, last, steps⟩ := grouped_boundaries history
  have noZero : ∀ row ∈ ordered, ∀ event ∈ row.memorySteps.map transferEvent,
      event.2.1 ≠ (Cell.register 0).addressCode := by
    intro row _ event included
    obtain ⟨edge, edgeMember, rfl⟩ := List.mem_map.mp included
    change edge ∈ row.ports.toList.map (fun port => (readToken row.assignment port, row.writeToken port)) at edgeMember
    obtain ⟨port, portMember, rfl⟩ : ∃ port ∈ row.ports.toList,
      (readToken row.assignment port, row.writeToken port) = edge := List.mem_map.mp edgeMember
    exact port_not_zero row (by simpa only [Array.mem_toList_iff] using portMember)
  have initial : ∀ cell ∈ cells, ∃ value, cell.read initial = .ok value initial := by
    intro cell member
    obtain ⟨_, _, value, read, _⟩ := image_cell_source inputs.initialization cell member
    exact ⟨value, read⟩
  have reads := boundary_reads count last steps aligned noZero initial
  refine ⟨states, count, head, last, reads, ?_⟩
  intro i bound
  obtain ⟨events, eventsPerm, current⟩ := steps i bound
  exact ⟨events, eventsPerm, current,
    row_atomic_observations hp accepted inputs (permutation.mem_iff.mp (List.getElem_mem _))
      current eventsPerm aligned (reads (i + 1) (by omega))⟩

end Airbender.Delegation.Proofs
