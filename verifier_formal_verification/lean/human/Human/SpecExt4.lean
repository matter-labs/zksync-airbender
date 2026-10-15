import Human.RV32
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # What `ext4_horner(COEFFS4, 32, y)` should compute: a polynomial over BabyBear's degree-4 extension -/

namespace Spec
open Polynomial

/-- The BabyBear field, `p = 2^31 - 2^27 + 1` (`RV.BabyBearP`, the prime of the field opcodes). -/
abbrev F := ZMod RV.BabyBearP

/-- Its degree-4 extension as in Airbender's `field` crate: `Ext2 = F[v]/(v² - 11)`, `Ext4 = Ext2[w]/(w² - v)`,
i.e. `F[w]/(w⁴ - 11)` with `v = w²`. -/
abbrev E4 := AdjoinRoot (X ^ 4 - C 11 : F[X])

/-- The generator `w` (`w⁴ = 11`). -/
noncomputable def w : E4 := AdjoinRoot.root _

/-- An element from its 4 limbs in the `field` crate's order `(c0.c0, c0.c1, c1.c0, c1.c1)`, the coefficients of
`1, v, w, v w`. -/
noncomputable def ofLimbs (l0 l1 l2 l3 : F) : E4 :=
  AdjoinRoot.of _ l0 + AdjoinRoot.of _ l1 * w ^ 2 + AdjoinRoot.of _ l2 * w + AdjoinRoot.of _ l3 * w ^ 3

/-- The coefficients of the polynomial (Rust `COEFFS4`): `cᵢ = (i + 1, 2 i + 3, i², 7)`. -/
noncomputable def coeff4 (i : ℕ) : E4 := ofLimbs (i + 1 : ℕ) (2 * i + 3 : ℕ) (i ^ 2 : ℕ) 7

/-- `∑_{i < 32} cᵢ yⁱ`. -/
noncomputable def poly4 (y : E4) : E4 := ∑ i ∈ Finset.range 32, coeff4 i * y ^ i

end Spec
