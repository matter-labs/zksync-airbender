import Airbender.Review.Helpers.Tables.ShiftScalars
import Mathlib.Tactic.IntervalCases

namespace Airbender.Verification.ShiftScalarProofs
set_option warningAsError true
set_option Elab.async false

/-- The two native-sized limbs reassemble the ordinary RV32 sign-fill mask,
    including the native unbounded-shift-by-32 behavior at shift zero. -/
theorem sign_mask (n : Nat) (bound : n < 2097152) :
    signFillLow n < 65536 ∧ signFillHigh n < 65536 ∧
      BitVec.ofNat 32 (signFillLow n + 65536 * signFillHigh n) =
        if n % 65536 < 32768 then 0 else (BitVec.allOnes 32) <<< (32 - n / 65536) := by
  have shifts : n / 65536 < 32 := by omega
  interval_cases shift : n / 65536
  all_goals
    by_cases sign : n % 65536 < 32768
    all_goals
      simp only [signFillLow,signFillHigh]
      first | simp only [if_pos sign] | simp only [if_neg sign]
      try simp_rw [shift]
      decide +kernel

end Airbender.Verification.ShiftScalarProofs
