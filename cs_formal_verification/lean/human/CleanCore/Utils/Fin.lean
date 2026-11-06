module
public import Mathlib.Algebra.BigOperators.Fin

/-! # `Fin.foldl` as a sum (Clean `Clean.Utils.Fin`, pinned 93c9d1e): transcribed with proofs. -/

@[expose] public section

namespace Airbender

namespace Fin
/-- Convert Fin.foldl to Finset.sum via range -/
theorem foldl_eq_sum_range {α : Type*} [AddCommMonoid α] : ∀ (n' : ℕ) (f' : Fin n' → α),
    Fin.foldl n' (fun acc i => acc + f' i) 0 = ∑ i ∈ Finset.range n', if h : i < n' then f' ⟨i, h⟩ else 0 := by
  intro n' f'
  induction n' with
  | zero =>
    simp [Fin.foldl_zero, Finset.range_zero]
  | succ n'' ih =>
    rw [Fin.foldl_succ_last]
    rw [Finset.sum_range_succ]
    simp only [ih]
    -- We need to show that the sum equals itself plus the last term
    congr 1
    -- For the sum part, we need to show the functions are equal
    · apply Finset.sum_congr rfl
      intro i hi
      simp only [Finset.mem_range] at hi
      simp only [Fin.castSucc_mk]
      simp only [hi]
      simp only [↓reduceDIte]
      have hi' : i < n'' + 1 := by omega
      simp only [hi', ↓reduceDIte]
    · -- For the last term
      simp only [Fin.last, Nat.lt_succ_self, dif_pos]

/-- Convert Fin.foldl to a standard sum -/
theorem foldl_to_sum {α : Type*} [AddCommMonoid α] : ∀ (n' : ℕ) (f' : Fin n' → α),
    Fin.foldl n' (fun acc i => acc + f' i) 0 = ∑ i : Fin n', f' i := by
  intro n' f'
  simp only [Finset.sum_fin_eq_sum_range]
  exact foldl_eq_sum_range n' f'

end Fin

end Airbender
