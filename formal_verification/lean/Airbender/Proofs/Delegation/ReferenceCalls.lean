import Airbender.Proofs.Delegation.CallState
import Mathlib.Logic.Relation

namespace Airbender.Delegation.Proofs
open Trace Reference.RiscV.Sail
set_option warningAsError true

theorem grouped_reference {rows : List α} {domain : List Cell} {initial after : State}
    {accesses : α → List MemoryAccess} {reference : State → State → Prop}
    (history : GroupedSailHistory domain accesses rows initial after)
    (aligned : ∀ cell ∈ domain, cell.Aligned)
    (noZero : ∀ row ∈ rows, ∀ event ∈ accesses row, event.2.1 ≠ (Cell.register 0).addressCode)
    (readable : ∀ cell ∈ domain, ∃ value, cell.read initial = .ok value initial)
    (step : ∀ row ∈ rows, ∀ {events before after},
      (∀ cell ∈ domain, ∃ value, cell.read before = .ok value before) →
      events.Perm (accesses row) → SailHistory domain events before after → reference before after) :
    Relation.ReflTransGen reference initial after := by
  induction history with
  | nil => exact .refl
  | @cons row rest initial middle after events past permutation current ih =>
    have noZeroPast := fun r m => noZero r (List.mem_cons_of_mem _ m)
    have earlier := ih noZeroPast readable (fun r m => step r (List.mem_cons_of_mem _ m))
    exact earlier.tail (step row List.mem_cons_self
      (grouped_readable past aligned noZeroPast readable) permutation current)

end Airbender.Delegation.Proofs
