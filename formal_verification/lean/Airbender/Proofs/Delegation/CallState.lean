import Airbender.Proofs.Delegation.Atomic
import Airbender.Proofs.Delegation.CallHistory

namespace Airbender.Delegation.Proofs
open Trace Trace.Proofs Reference.RiscV.Sail
set_option warningAsError true

theorem grouped_readable {rows : List α} {cells : List Cell} {before after : State}
    {accesses : α → List MemoryAccess} (history : GroupedSailHistory cells accesses rows before after)
    (aligned : ∀ cell ∈ cells, cell.Aligned)
    (noZero : ∀ row ∈ rows, ∀ event ∈ accesses row, event.2.1 ≠ (Cell.register 0).addressCode)
    (initial : ∀ cell ∈ cells, ∃ value, cell.read before = .ok value before) :
    ∀ cell ∈ cells, ∃ value, cell.read after = .ok value after := by
  induction history with
  | nil => exact initial
  | @cons row rest before middle after events past permutation current ih =>
    have earlier := ih (fun r m => noZero r (List.mem_cons_of_mem _ m)) initial
    exact history_readable current aligned
      (fun e m => noZero row List.mem_cons_self e (permutation.mem_iff.mp m)) earlier

theorem grouped_positions {rows : List α} {cells : List Cell} {before after : State}
    {accesses : α → List MemoryAccess} (history : GroupedSailHistory cells accesses rows before after)
    (aligned : ∀ cell ∈ cells, cell.Aligned)
    (noZero : ∀ row ∈ rows, ∀ event ∈ accesses row, event.2.1 ≠ (Cell.register 0).addressCode)
    (initial : ∀ cell ∈ cells, ∃ value, cell.read before = .ok value before) :
    ∀ row ∈ rows, ∃ events start finish, events.Perm (accesses row) ∧
      SailHistory cells events start finish ∧
      ∀ cell ∈ cells, ∃ value, cell.read start = .ok value start := by
  induction history with
  | nil => intro row member; cases member
  | @cons row rest before middle after events past permutation current ih =>
    intro r member
    rcases List.mem_cons.mp member with equal | member
    · subst r
      exact ⟨events, middle, after, permutation, current,
        grouped_readable past aligned (fun r m => noZero r (List.mem_cons_of_mem _ m)) initial⟩
    · exact ih (fun r m => noZero r (List.mem_cons_of_mem _ m)) initial r member

end Airbender.Delegation.Proofs
