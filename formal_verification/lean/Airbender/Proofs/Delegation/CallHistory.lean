import Airbender.Proofs.Delegation.CallGroups
import Airbender.Review.Delegation.Execution
import Airbender.Proofs.Trace.RowHistory

namespace Airbender.Delegation.Proofs
open Trace Trace.Proofs Reference.RiscV.Sail
set_option warningAsError true

inductive GroupedSailHistory (cells : List Cell) (accesses : α → List MemoryAccess) :
    List α → State → State → Prop where
  | nil (before) : GroupedSailHistory cells accesses [] before before
  | cons {row rest before middle after events}
      (past : GroupedSailHistory cells accesses rest before middle)
      (permutation : events.Perm (accesses row))
      (current : SailHistory cells events middle after) :
      GroupedSailHistory cells accesses (row :: rest) before after

theorem grouped_history {rows : List α} {events : List MemoryAccess}
    {cells : List Cell} {before after : State} (clock : α → Nat) (accesses : α → List MemoryAccess)
    (rowOrder : rows.Pairwise (fun a b => clock b < clock a))
    (eventOrder : events.Pairwise (fun a b => b.1 ≤ a.1))
    (permutation : events.Perm (rows.flatMap accesses))
    (times : ∀ row ∈ rows, ∀ event ∈ accesses row, event.1 = clock row)
    (history : SailHistory cells events before after) :
    GroupedSailHistory cells accesses rows before after := by
  have coverage : ∀ event ∈ events, ∃ row ∈ rows, event.1 = clock row := by
    intro event member
    obtain ⟨row, included, present⟩ := List.mem_flatMap.mp (permutation.mem_iff.mp member)
    exact ⟨row, included, times row included event present⟩
  have grouped := group_call_events clock rowOrder eventOrder coverage
  have unique : (rows.map clock).Nodup := by
    apply List.pairwise_map.mpr
    exact rowOrder.imp (by intro a b less; omega)
  have groups : ∀ row ∈ rows,
      (events.filter fun event => decide (event.1 = clock row)).Perm (accesses row) :=
    fun row member => call_group_perm clock accesses unique permutation times member
  rw [← grouped] at history
  clear permutation times coverage grouped eventOrder unique rowOrder
  induction rows generalizing after with
  | nil => cases history; exact .nil before
  | cons row rest ih =>
    rw [List.flatMap_cons] at history
    obtain ⟨middle, past, current⟩ := sail_history_append.mp history
    exact .cons (ih past (fun later member => groups later (List.mem_cons_of_mem _ member)))
      (groups row List.mem_cons_self) current


theorem ungrouped_history {rows : List α} {cells : List Cell} {accesses : α → List MemoryAccess}
    {before after : State} (history : GroupedSailHistory cells accesses rows before after) :
    ∃ events, events.Perm (rows.flatMap accesses) ∧ SailHistory cells events before after := by
  induction history with
  | nil => exact ⟨[], List.Perm.refl _, .nil _⟩
  | @cons row rest before middle after events past permutation current ih =>
    obtain ⟨earlier, earlierPerm, earlierHistory⟩ := ih
    exact ⟨events ++ earlier, by simpa only [List.flatMap_cons] using permutation.append earlierPerm,
      sail_history_append.mpr ⟨middle, earlierHistory, current⟩⟩

end Airbender.Delegation.Proofs
