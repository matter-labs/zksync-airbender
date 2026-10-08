import Airbender.Proofs.Bigint.MultiplicationRanges
import Airbender.Proofs.Bigint.MultiplicationFields
import Airbender.Proofs.BabyBear

namespace Tests.BigintMultiplication
open Airbender Bigint.Multiplication.Proofs

theorem incorrectLowByteRejected (w : Nat → ZMod babyBearModulus)
    (source : w 5 = 65535) (wrong : w 99 = 0) :
    ¬ FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (Bigint.importedConstraints Bigint.setupTable) := by
  intro row
  have low := (source_low_bytes (by decide) row 0).1
  have sourceValue : (65535 : ZMod babyBearModulus).val = 65535 := by decide
  norm_num [Bigint.Variables.leftLimbs, source, wrong, sourceValue, babyBearModulus] at low
  exact (by decide : (0 : ZMod babyBearModulus) ≠ 255) low

theorem oversizedCarryRejected (w : Nat → ZMod babyBearModulus) (i : Fin 31)
    (oversized : 8192 ≤ (carry w i).val) :
    ¬ FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (Bigint.importedConstraints Bigint.setupTable) := by
  intro row
  have bound := carry_bounded (by decide) row i
  omega

/-- The paired nine-bit query also ranges its second carry, not just its first. -/
theorem pairedCarryRejected (w : Nat → ZMod babyBearModulus)
    (oversized : 512 ≤ (carry w 30).val) :
    ¬ FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (Bigint.importedConstraints Bigint.setupTable) := by
  intro row
  have bound := carry_ranges (by decide) row 30
  change (carry w 30).val < 512 at bound
  omega

theorem lowProductOverflowRejected
    (setup : Table (ZMod babyBearModulus) (fields 3)) (w : Nat → ZMod babyBearModulus)
    (selected : w 62 = 1 ∨ w 63 = 1) (oversized : 65536 ≤ (w 131).val) :
    ¬ FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (Bigint.importedConstraints setup) := by
  intro row
  have bound := product_ranges (by decide) row selected 0
  simp only [Arithmetic.limbBase, Fin.val_zero, Nat.add_zero] at bound
  omega

theorem maximalLimbBytes :
    (255 : ZMod babyBearModulus).val < 256 ∧
      (65535 : ZMod babyBearModulus).val / 256 < 256 ∧
      (65535 : ZMod babyBearModulus) = 255 +
        256 * (((65535 : ZMod babyBearModulus).val / 256 : Nat) : ZMod babyBearModulus) :=
  limb_bytes (by decide) (by decide)

end Tests.BigintMultiplication
