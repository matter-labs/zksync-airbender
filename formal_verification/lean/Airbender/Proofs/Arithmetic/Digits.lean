import Airbender.Proofs.Arithmetic.CarryChain
import Mathlib.Algebra.BigOperators.Fin

namespace Airbender.Arithmetic
open scoped BigOperators
set_option warningAsError true

theorem limb_sum_bound {radix length : Nat} (positive : 0 < radix) {limbs : Nat → Nat}
    (bounded : ∀ i < length, limbs i < radix) :
    limbSum radix length limbs < radix ^ length := by
  induction length with
  | zero => simp [limbSum]
  | succ n prior =>
    have initial := prior (fun i small => bounded i (by omega))
    have last := bounded n (by omega)
    have product := Nat.mul_le_mul_left (radix ^ n) (by omega : limbs n ≤ radix - 1)
    have total : radix ^ n + radix ^ n * (radix - 1) = radix ^ (n + 1) := by
      rw [pow_succ]
      calc
        _ = radix ^ n * (1 + (radix - 1)) := by ring
        _ = _ := by congr 1; omega
    simp only [limbSum, Finset.sum_range_succ] at initial ⊢
    omega

theorem weighted_limb_bound {radix length : Nat} (positive : 0 < radix)
    {limbs : Fin length → Nat} (bounded : ∀ i, limbs i < radix) :
    (∑ i : Fin length, radix ^ i.val * limbs i) < radix ^ length := by
  let extended : Nat → Nat := fun i => if small : i < length then limbs ⟨i, small⟩ else 0
  have bound := limb_sum_bound (length := length) positive (limbs := extended)
    (fun i small => by simpa only [extended, small, ↓reduceDIte] using bounded ⟨i, small⟩)
  unfold limbSum at bound
  rw [← Fin.sum_univ_eq_sum_range] at bound
  simpa [extended] using bound

theorem weighted_sum_zero {radix length : Nat} (positive : 0 < radix)
    {limbs : Fin length → Nat} :
    ((∑ i : Fin length, radix ^ i.val * limbs i) = 0) ↔ ∀ i, limbs i = 0 := by
  constructor
  · intro zeros i
    have zero := Finset.sum_eq_zero_iff.mp zeros i (Finset.mem_univ i)
    exact (Nat.mul_eq_zero.mp zero).resolve_left (Nat.ne_of_gt (pow_pos positive _))
  · intro zeros
    simp only [zeros, Nat.mul_zero, Finset.sum_const_zero]

/-- A sum of canonical field limbs below the characteristic cannot hide a
    nonzero limb by wrapping. Shared by zero tests in EQ and multiplication. -/
theorem field_sum_zero {p length : Nat} [Fact p.Prime] {limbs : Fin length → ZMod p}
    (bounded : (∑ i, (limbs i).val) < p) :
    ((∑ i, limbs i) = 0) ↔ ∀ i, (limbs i).val = 0 := by
  have castSum : ((∑ i, (limbs i).val : Nat) : ZMod p) = ∑ i, limbs i := by
    simp only [Nat.cast_sum, ZMod.natCast_zmod_val]
  constructor
  · intro zero
    have natural : (∑ i, (limbs i).val) = 0 := bounded_nat_eq (F := ZMod p) (p := p)
      bounded (by exact (Fact.out : p.Prime).pos) (by simpa only [zero, Nat.cast_zero] using castSum)
    exact fun i => Finset.sum_eq_zero_iff.mp natural i (Finset.mem_univ i)
  · intro zeros
    have natural : (∑ i, (limbs i).val) = 0 := Finset.sum_eq_zero_iff.mpr (fun i _ => zeros i)
    rw [← castSum, natural, Nat.cast_zero]

theorem product_halves {modulus product low high : Nat} (positive : 0 < modulus)
    (bounded : low < modulus) (equation : product = low + modulus * high) :
    product % modulus = low ∧ product / modulus = high ∧
      (modulus ≤ product ↔ high ≠ 0) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [equation, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt bounded]
  · rw [equation, Nat.add_mul_div_left _ _ positive, Nat.div_eq_of_lt bounded, Nat.zero_add]
  · constructor
    · intro overflow zero
      simp only [zero, Nat.mul_zero, Nat.add_zero] at equation
      omega
    · intro nonzero
      have atLeast := Nat.mul_le_mul_left modulus (by omega : 1 ≤ high)
      rw [Nat.mul_one] at atLeast
      omega

end Airbender.Arithmetic
