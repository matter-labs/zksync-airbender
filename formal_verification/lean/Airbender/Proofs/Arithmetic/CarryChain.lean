import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Proofs.Arithmetic.Lemmas

namespace Airbender.Arithmetic
open scoped BigOperators
set_option warningAsError true

def limbSum (radix length : Nat) (limbs : Nat → Nat) : Nat :=
  ∑ i ∈ Finset.range length, radix ^ i * limbs i

/-- A finite carry recurrence composes into an exact multi-limb equation. -/
theorem carry_chain {radix length : Nat} {left right result carry : Nat → Nat}
    (steps : ∀ i < length, left i + right i + carry i = result i + radix * carry (i + 1)) :
    limbSum radix length left + limbSum radix length right + carry 0 =
      limbSum radix length result + radix ^ length * carry length := by
  induction length with
  | zero => simp [limbSum]
  | succ n ih =>
    have initial := ih (fun i hi => steps i (by omega))
    have last := congrArg (fun value => radix ^ n * value) (steps n (by omega))
    simp only [limbSum, Finset.sum_range_succ, pow_succ] at *
    ring_nf at initial last ⊢
    omega

theorem bounded_carry_step {F : Type} [CommRing F] {p radix a b r c d : Nat} [CharP F p]
    (hp : FieldCapacity.AtLeast p (2 * radix)) (ha : a < radix) (hb : b < radix) (hr : r < radix)
    (hc : c ≤ 1) (hd : d ≤ 1)
    (field : (a : F) + b + c = r + (radix : F) * d) : a + b + c = r + radix * d := by
  have bound : radix * d ≤ radix := by simpa using Nat.mul_le_mul_left radix hd
  exact bounded_nat_eq (F := F) (p := p) (by omega) (by omega) (by exact_mod_cast field)

private theorem zero_borrow_step {radix a b r c : Nat}
    (rb : r < radix) (bb : b < radix) (cb : c ≤ 1)
    (step : r + b = a + radix * c) (zero : r = 0 ∨ a = b) :
    r = 0 ∧ a = b ∧ c = 0 := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp cb with c0 | c1
  · rw [c0, Nat.mul_zero, Nat.add_zero] at step
    rcases zero with rz | same <;> omega
  · rw [c1, Nat.mul_one] at step
    rcases zero with rz | same <;> omega

theorem subtraction_zero {radix length : Nat} {left right result carry : Nat → Nat}
    (steps : ∀ i < length, result i + right i + carry i = left i + radix * carry (i + 1))
    (resultBound : ∀ i < length, result i < radix)
    (rightBound : ∀ i < length, right i < radix)
    (carryBound : ∀ i ≤ length, carry i ≤ 1) (initial : carry 0 = 0) :
    ((∀ i < length, result i = 0) ↔ ∀ i < length, left i = right i) ∧
    ((∀ i < length, result i = 0) → carry length = 0) := by
  induction length with
  | zero => simp [initial]
  | succ n ih =>
    have prefixResult := fun i (hi : i < n) => resultBound i (by omega)
    have prefixRight := fun i (hi : i < n) => rightBound i (by omega)
    have prefixCarry := fun i (hi : i ≤ n) => carryBound i (by omega)
    have prior := ih (fun i hi => steps i (by omega)) prefixResult prefixRight prefixCarry
    have next (zeros : ∀ i < n, result i = 0) (last : result n = 0 ∨ left n = right n) :
        result n = 0 ∧ left n = right n ∧ carry (n + 1) = 0 := by
      have step := steps n (by omega)
      rw [prior.2 zeros, Nat.add_zero] at step
      exact zero_borrow_step (resultBound n (by omega)) (rightBound n (by omega))
        (carryBound (n + 1) (by omega)) step last
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro zeros i hi
      by_cases before : i < n
      · exact prior.1.mp (fun j hj => zeros j (by omega)) i before
      · have eq : i = n := by omega
        subst i
        exact (next (fun j hj => zeros j (by omega)) (Or.inl (zeros n (by omega)))).2.1
    · intro same i hi
      have zeros := prior.1.mpr (fun j hj => same j (by omega))
      by_cases before : i < n
      · exact zeros i before
      · have eq : i = n := by omega
        subst i
        exact (next zeros (Or.inr (same n (by omega)))).1
    · intro zeros
      exact (next (fun j hj => zeros j (by omega)) (Or.inl (zeros n (by omega)))).2.2

end Airbender.Arithmetic
