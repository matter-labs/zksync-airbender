import Airbender.Proofs.Memory.DelegationSum
import Airbender.Proofs.Tables.NormalizeLast
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Algebra.Polynomial.RingDivision

namespace Airbender.Delegation.SumCompletionProofs
open Polynomial
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

theorem full_sum {R : Type} [Field R] {n : Nat} {omega : R} {p : R[X]}
    (primitive : IsPrimitiveRoot omega n) (small : p.natDegree < n) :
    (∑ i ∈ Finset.range n, p.eval (omega^i)) = (n : R)*p.eval 0 := by
  classical
  have formula : (∑ i ∈ Finset.range n, p.eval (omega^i)) = (n : R)*p.coeff 0 := by
    simp_rw [Polynomial.eval_eq_sum,Polynomial.sum]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    rw [Finset.sum_eq_single 0]
    · simp [mul_comm]
    · intro exponent present nonzero
      have bound := lt_of_le_of_lt
        (Polynomial.le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp present)) small
      rw [SumProofs.powers_sum primitive nonzero bound,mul_zero]
    · intro absent
      have coeffZero : p.coeff 0 = 0 := by
        by_contra nonzero
        exact absent (Polynomial.mem_support_iff.mpr nonzero)
      rw [coeffZero,zero_mul]
  simpa only [Polynomial.coeff_zero_eq_eval_zero] using formula

theorem boundary_of_values {R : Type} [Field R] {n : Nat} {omega claimed : R} {p : R[X]}
    (positive : 0 < n) (primitive : IsPrimitiveRoot omega n)
    (zero : p.eval 0 = 0) (last : p.eval (omega^(n-1)) = -claimed) :
    X*(X-C (omega^(n-1))) ∣ p+C (claimed*omega)*X := by
  have lastPower : omega*omega^(n-1) = 1 := by
    rw [← pow_succ',Nat.sub_add_cancel positive,primitive.pow_eq_one]
  have lastNonzero : omega^(n-1) ≠ 0 := by
    intro eqn
    rw [eqn,mul_zero] at lastPower
    exact zero_ne_one lastPower
  have atZero : X ∣ p+C (claimed*omega)*X := by
    rw [Polynomial.X_dvd_iff,Polynomial.coeff_zero_eq_eval_zero]
    simp [zero]
  have atLast : X-C (omega^(n-1)) ∣ p+C (claimed*omega)*X := by
    rw [Polynomial.dvd_iff_isRoot,Polynomial.IsRoot.def]
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,last,
      mul_assoc,lastPower,mul_one,neg_add_cancel]
  have coprime : IsCoprime X (X-C (omega^(n-1))) := by
    simpa only [map_zero,sub_zero] using
      (Polynomial.isCoprime_X_sub_C_of_isUnit_sub (a := (0 : R)) (b := omega^(n-1))
        (sub_ne_zero.mpr (Ne.symm lastNonzero)).isUnit)
  exact coprime.mul_dvd atZero atLast

theorem normalized_completion {R : Type} [Field R] {n : Nat} {omega : R}
    (positive : 0 < n) (primitive : IsPrimitiveRoot omega n) (castNonzero : (n : R) ≠ 0)
    (rows : Nat → R) :
    ∃ p, SumPolynomialAccepted n omega p (Verification.normalizeLast n rows)
      (∑ i ∈ Finset.range (n-1), rows i) := by
  classical
  let values := Verification.normalizeLast n rows
  let p := Lagrange.interpolate (Finset.range n) (fun i => omega^i) values
  have injective : Set.InjOn (fun i => omega^i) (Finset.range n) := by
    intro i hi j hj same
    exact primitive.pow_inj (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) same
  have degree : p.natDegree < n := by
    by_cases zero : p = 0
    · simpa only [zero,Polynomial.natDegree_zero] using positive
    · apply (Polynomial.natDegree_lt_iff_degree_lt zero).mpr
      simpa only [Finset.card_range] using Lagrange.degree_interpolate_lt values injective
  have samples : ∀ i < n, p.eval (omega^i) = values i := by
    intro i small
    exact Lagrange.eval_interpolate_at_node values injective (Finset.mem_range.mpr small)
  have atZero : p.eval 0 = 0 := by
    have total := full_sum primitive degree
    have observations : (∑ i ∈ Finset.range n, p.eval (omega^i)) = 0 := by
      rw [Finset.sum_congr rfl (fun i hi => samples i (Finset.mem_range.mp hi))]
      exact Verification.NormalizeLastProofs.domain_sum positive rows
    rw [observations] at total
    exact (mul_eq_zero.mp total.symm).resolve_left castNonzero
  refine ⟨p,positive,primitive,degree,samples,?_⟩
  apply boundary_of_values positive primitive atZero
  rw [samples (n-1) (by omega)]
  exact Verification.NormalizeLastProofs.terminal n rows
theorem not_constant {R : Type} [Field R] {n : Nat} {omega claimed : R} {p : R[X]}
    {values : Nat → R} (accepted : SumPolynomialAccepted n omega p values claimed)
    (nonzero : claimed ≠ 0) (constant : R) : p ≠ C constant := by
  intro same
  obtain ⟨zero,last⟩ := SumProofs.boundary_values accepted
  rw [same,Polynomial.eval_C] at zero last
  rw [zero] at last
  exact nonzero (neg_eq_zero.mp last.symm)
end Airbender.Delegation.SumCompletionProofs
