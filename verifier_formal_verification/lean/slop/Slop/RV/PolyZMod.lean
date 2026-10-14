import Slop.RV.Coeffs
import Human.SpecPoly
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! From the `Nat` Horner value of the coefficient table to the `ZMod P` polynomial of the human spec. -/

namespace RV

theorem polyW_sum (c : List Word) (x : Nat) :
    polyW c x = ∑ i ∈ Finset.range c.length, c[i]!.toNat * x ^ i := by
  induction c with
  | nil => rfl
  | cons a l ih =>
    rw [List.length_cons, Finset.sum_range_succ']
    simp only [polyW, List.foldr_cons] at ih ⊢
    rw [ih, Finset.mul_sum]
    simp only [List.getElem!_cons_succ, List.getElem!_cons_zero, pow_zero, mul_one]
    rw [Nat.add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring

theorem coeffs_spec_check : (List.range 100).all (fun i => (Code.COEFFS[i]!).toNat == Spec.coeffNat i) = true := by
  decide +kernel

theorem coeffs_val (i : Nat) (h : i < 100) : (Code.COEFFS[i]!).toNat = Spec.coeffNat i := by
  exact beq_iff_eq.mp (List.all_eq_true.mp coeffs_spec_check i (List.mem_range.mpr h))

theorem polyW_zmod (x : Nat) : ((polyW Code.COEFFS x : Nat) : ZMod Spec.P) = Spec.poly (x : ZMod Spec.P) := by
  rw [polyW_sum, coeffs_length, Spec.poly]
  push_cast
  apply Finset.sum_congr rfl
  intro i hi
  rw [coeffs_val i (Finset.mem_range.mp hi), Spec.coeff]

end RV
