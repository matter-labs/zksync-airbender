import Airbender.Proofs.Memory.DelegationSum

namespace Airbender.Delegation

theorem native_sum {R : Type} [Field R] {n : Nat} {omega : R} {p : Polynomial R}
    {values : Nat → R} {claimed : R} (accepted : SumPolynomialAccepted n omega p values claimed) :
    (∑ i ∈ Finset.range (n-1), values i) = claimed :=
  SumProofs.ordinary_sum accepted

end Airbender.Delegation
