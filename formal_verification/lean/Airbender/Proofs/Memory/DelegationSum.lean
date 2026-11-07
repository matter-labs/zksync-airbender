import Airbender.Review.Helpers.Memory.DelegationSum
import Mathlib.Tactic.Ring

namespace Airbender.Delegation.SumProofs
open Polynomial
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

theorem powers_sum {R : Type} [Field R] {n : Nat} {omega : R}
    (primitive : IsPrimitiveRoot omega n) {exponent : Nat} (positive : exponent ≠ 0) (small : exponent < n) :
    (∑ i ∈ Finset.range n, (omega^i)^exponent) = 0 := by
  have ne := primitive.pow_ne_one_of_pos_of_lt positive small
  have power : (omega^exponent)^n = 1 := by
    rw [← pow_mul,Nat.mul_comm,pow_mul,primitive.pow_eq_one,one_pow]
  have zero : (∑ i ∈ Finset.range n, (omega^exponent)^i) = 0 := by
    refine eq_zero_of_ne_zero_of_mul_left_eq_zero (sub_ne_zero_of_ne ne.symm) ?_
    rw [mul_neg_geom_sum,power,sub_self]
  simpa only [← pow_mul,Nat.mul_comm] using zero

theorem full_sum_zero {R : Type} [Field R] {n : Nat} {omega : R} {p : R[X]}
    (primitive : IsPrimitiveRoot omega n) (small : p.natDegree < n) (zero : p.eval 0 = 0) :
    (∑ i ∈ Finset.range n, p.eval (omega^i)) = 0 := by
  classical
  simp_rw [Polynomial.eval_eq_sum,Polynomial.sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro exponent present
  rw [← Finset.mul_sum]
  by_cases isZero : exponent = 0
  · subst exponent
    rw [Polynomial.coeff_zero_eq_eval_zero,zero,zero_mul]
  · have bound := lt_of_le_of_lt (Polynomial.le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp present)) small
    rw [powers_sum primitive isZero bound,mul_zero]

theorem boundary_values {R : Type} [Field R] {n : Nat} {omega : R} {p : R[X]}
    {values : Nat → R} {claimed : R} (accepted : SumPolynomialAccepted n omega p values claimed) :
    p.eval 0 = 0 ∧ p.eval (omega^(n-1)) = -claimed := by
  obtain ⟨q,eqn⟩ := accepted.boundary
  have atZero := congrArg (Polynomial.eval (0 : R)) eqn
  have atLast := congrArg (Polynomial.eval (omega^(n-1))) eqn
  have lastPower : omega*omega^(n-1) = 1 := by
    rw [← pow_succ',Nat.sub_add_cancel accepted.positive,accepted.primitive.pow_eq_one]
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_X,Polynomial.eval_C,
    mul_zero,add_zero,zero_mul,Polynomial.eval_sub,sub_self] at atZero atLast
  have literal : claimed*omega*omega^(n-1) = claimed := by
    rw [mul_assoc,lastPower,mul_one]
  rw [literal] at atLast
  exact ⟨atZero,eq_neg_of_add_eq_zero_left atLast⟩

theorem ordinary_sum {R : Type} [Field R] {n : Nat} {omega : R} {p : R[X]}
    {values : Nat → R} {claimed : R} (accepted : SumPolynomialAccepted n omega p values claimed) :
    (∑ i ∈ Finset.range (n-1), values i) = claimed := by
  have endpoints := boundary_values accepted
  have total := full_sum_zero accepted.primitive accepted.degree endpoints.1
  have positive := accepted.positive
  have domain : n = (n-1)+1 := by omega
  rw [domain,Finset.sum_range_succ] at total
  rw [endpoints.2] at total
  have samples : (∑ i ∈ Finset.range (n-1), p.eval (omega^i)) =
      ∑ i ∈ Finset.range (n-1), values i := by
    apply Finset.sum_congr rfl
    intro i hi
    exact accepted.samples i (by have := Finset.mem_range.mp hi; omega)
  rw [samples] at total
  exact sub_eq_zero.mp (by simpa only [sub_eq_add_neg] using total)

end Airbender.Delegation.SumProofs
