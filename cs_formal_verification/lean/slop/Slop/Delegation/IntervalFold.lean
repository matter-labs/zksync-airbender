import Slop.Delegation.ReverseFold

namespace Airbender.Delegation.Proofs
set_option warningAsError true

theorem interval_fold (states : Nat → α) (step : Nat → α → α) (start count : Nat)
    (transitions : ∀ i < count, states (start + i + 1) = step (start + i) (states (start + i))) :
    states (start + count) =
      Fin.foldl count (fun state i => step (start + i.val) state) (states start) := by
  have prefixResult : ∀ k ≤ count, states (start + k) =
      Fin.foldl k (fun state i => step (start + i.val) state) (states start) := by
    intro k
    induction k with
    | zero => intro bound; simp only [Nat.add_zero, Fin.foldl_zero]
    | succ k ih =>
      intro bound
      have index : start + (k + 1) = start + k + 1 := by omega
      rw [index, transitions k (by omega), ih (by omega), Fin.foldl_succ_last]
      rfl
  exact prefixResult count (by omega)

end Airbender.Delegation.Proofs
