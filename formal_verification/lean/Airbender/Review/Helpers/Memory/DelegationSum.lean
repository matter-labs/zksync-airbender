import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.Polynomial.BigOperators

namespace Airbender.Delegation
open Polynomial

/-- Reviewed native last-row/zero divisor and linear interpolant, after
    normalization of the auxiliary polynomial. Physical LDE/quotient/challenge
    separation and Rust/FFT refinement are separate. The sum is not a premise. -/
structure SumPolynomialAccepted {R : Type} [Field R] (size : Nat) (omega : R)
    (polynomial : R[X]) (values : Nat → R) (claimed : R) : Prop where
  positive : 0 < size
  primitive : IsPrimitiveRoot omega size
  degree : polynomial.natDegree < size
  samples : ∀ i < size, polynomial.eval (omega^i) = values i
  boundary : X * (X-C (omega^(size-1))) ∣ polynomial + C (claimed*omega)*X

end Airbender.Delegation
