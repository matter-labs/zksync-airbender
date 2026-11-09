import Airbender.Proofs.Memory.DelegationSumCompletion

namespace Airbender.Delegation
/-- Actual normalized observations admit a sum polynomial on a nondegenerate
    primitive domain. This is algebraic existence, not physical FFT refinement. -/
theorem normalized_sum_polynomial {R : Type} [Field R] {n : Nat} {omega : R}
    (positive : 0 < n) (primitive : IsPrimitiveRoot omega n) (castNonzero : (n : R) ≠ 0)
    (rows : Nat → R) :
    ∃ p, SumPolynomialAccepted n omega p (Verification.normalizeLast n rows)
      (∑ i ∈ Finset.range (n-1), rows i) :=
  SumCompletionProofs.normalized_completion positive primitive castNonzero rows
end Airbender.Delegation
