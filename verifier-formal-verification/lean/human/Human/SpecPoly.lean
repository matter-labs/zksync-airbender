import Human.Spec
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # What `poly_eval(COEFFS, 100, x)` should compute: a polynomial over the Mersenne31 field -/

namespace Spec

/-- The Mersenne31 prime `2^31 - 1` (Airbender's base field). -/
abbrev P : ℕ := 2 ^ 31 - 1

/-- The coefficients `coeffNat i` (`Spec.lean`) as field elements. -/
def coeff (i : ℕ) : ZMod P := coeffNat i

/-- `∑_{i < 100} cᵢ xⁱ`. -/
def poly (x : ZMod P) : ZMod P := ∑ i ∈ Finset.range 100, coeff i * x ^ i

end Spec
