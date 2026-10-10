import Batteries.Data.Fin.Fold
import Mathlib.Tactic

namespace Airbender.Delegation.Proofs
set_option warningAsError true

theorem reverse_fold {n : Nat} (states : Fin (n + 1) → α) (step : Nat → α → α)
    (transitions : ∀ i : Fin n,
      states ⟨i.val, by omega⟩ = step (n - 1 - i.val) (states ⟨i.val + 1, by omega⟩)) :
    states ⟨0, by omega⟩ = Fin.foldl n (fun state i => step i.val state) (states ⟨n, by omega⟩) := by
  have prefixResult : ∀ (k : Nat) (bound : k ≤ n),
      states ⟨n - k, by omega⟩ =
        Fin.foldl k (fun state i => step i.val state) (states ⟨n, by omega⟩) := by
    intro k
    induction k with
    | zero => intro bound; simp only [Nat.sub_zero, Fin.foldl_zero]
    | succ k ih =>
      intro bound
      have current := transitions ⟨n - (k + 1), by omega⟩
      have index : n - 1 - (n - (k + 1)) = k := by omega
      have previous : n - (k + 1) + 1 = n - k := by omega
      have current : states ⟨n - (k + 1), by omega⟩ = step k (states ⟨n - k, by omega⟩) := by
        simpa only [index, previous] using current
      rw [current, ih (by omega), Fin.foldl_succ_last]
      rfl
  simpa only [Nat.sub_self] using prefixResult n (by omega)

theorem reverse_constant {n : Nat} (states : Fin (n + 1) → α)
    (transitions : ∀ i : Fin n,
      states ⟨i.val, by omega⟩ = states ⟨i.val + 1, by omega⟩) :
    ∀ i : Fin (n + 1), states i = states ⟨n, by omega⟩ := by
  have prefixResult : ∀ (k : Nat) (bound : k ≤ n),
      states ⟨n - k, by omega⟩ = states ⟨n, by omega⟩ := by
    intro k
    induction k with
    | zero => intro bound; rfl
    | succ k ih =>
      intro bound
      have current := transitions ⟨n - (k + 1), by omega⟩
      have previous : n - (k + 1) + 1 = n - k := by omega
      have current : states ⟨n - (k + 1), by omega⟩ = states ⟨n - k, by omega⟩ := by
        simpa only [previous] using current
      exact current.trans (ih (by omega))
  intro i
  have index : n - (n - i.val) = i.val := by omega
  simpa only [index] using prefixResult (n - i.val) (by omega)

end Airbender.Delegation.Proofs
