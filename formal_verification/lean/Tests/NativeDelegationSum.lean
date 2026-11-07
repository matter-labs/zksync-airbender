import Airbender.Review.Helpers.Memory.DelegationSumTheorems
import Mathlib.Tactic.NormNum

namespace Airbender.Tests.NativeDelegationSum
open Polynomial Airbender.Delegation
set_option autoImplicit false

private def samples (i : Nat) : ℚ := if i = 0 then 3 else -3

/-- Positive two-slot polynomial/divisor example, not a native worker witness. -/
theorem positive_polynomial : SumPolynomialAccepted 2 (-1 : ℚ) (C 3*X) samples 3 := by
  refine ⟨by decide,IsPrimitiveRoot.neg_one 0 (by decide),?_,?_,?_⟩
  · norm_num
  · intro i hi
    have cases : i = 0 ∨ i = 1 := by omega
    rcases cases with rfl | rfl <;> norm_num [samples]
  · refine ⟨0,?_⟩
    norm_num

theorem positive_sum : (∑ i ∈ Finset.range 1, samples i) = 3 :=
  native_sum positive_polynomial

theorem zero_and_last : (C (3 : ℚ)*X).eval 0 = 0 ∧ (C (3 : ℚ)*X).eval (-1) = -3 := by
  norm_num

/-- A degree2 alias satisfies the endpoint divisor on a size2 domain. The
    native degree bound is essential; no counterexample to the full interface. -/
theorem high_degree_boundary : (X*(X-C ((-1 : ℚ)^(2-1)))) ∣
    X^2 + C ((-1 : ℚ)*(-1))*X := by
  refine ⟨1,?_⟩
  norm_num
  ring

theorem high_degree_rejected : ¬ SumPolynomialAccepted 2 (-1 : ℚ) (X^2) (fun _ => 1) (-1) := by
  intro accepted
  have impossible := accepted.degree
  norm_num at impossible

theorem endpoint_only_not_sum : (X^2 : Polynomial ℚ).eval 1 ≠ -1 := by norm_num

theorem wrong_public_claim_rejected : ¬ SumPolynomialAccepted 2 (-1 : ℚ) (C 3*X) samples 4 := by
  intro accepted
  have result := native_sum accepted
  norm_num [samples] at result

theorem nonzero_constant_rejected : ¬ SumPolynomialAccepted 2 (-1 : ℚ) (C 1) (fun _ => 1) (-1) := by
  intro accepted
  have zero := (SumProofs.boundary_values accepted).1
  norm_num at zero

end Airbender.Tests.NativeDelegationSum
