import Airbender.Review.Word
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace Airbender.Bigint
open scoped BigOperators

/-- Sixteen little-endian 16-bit limbs encode a 256-bit integer. -/
def value (limbs : Vector Nat 16) : Nat := ∑ i : Fin 16, Arithmetic.limbBase ^ i.val * limbs[i]

/-- Actual memory write and the x12 carry/borrow/Boolean response. -/
structure Output where
  result : Vector Nat 16
  control : Arithmetic.Word

end Airbender.Bigint
