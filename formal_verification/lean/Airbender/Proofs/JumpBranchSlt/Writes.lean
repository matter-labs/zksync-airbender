import Airbender.Proofs.JumpBranchSlt.PC
import Airbender.Proofs.Arithmetic.Lemmas

namespace Airbender.JumpBranchSlt.Proofs
open Verification Arithmetic

/-- Actual native masked destination: zero, the ranged link, or a one-bit value. -/
theorem written_limb_bounds {w : Nat → ZMod mersenne31Modulus}
    (native : FlatOperation.ConstraintsHoldFlat (environment w) importedConstraints)
    (mask : (w 12).val ∈ [1,2,4,8,16]) (flag : w 8 = 0 ∨ w 8 = 1) :
    (Word.mk (w 38).val (w 39).val).Bounded := by
  have link := assertion_of_holds native ⟨20, by rw [constraint_count]; decide⟩
  have comparison := assertion_of_holds native ⟨21, by rw [constraint_count]; decide⟩
  have low := assertion_of_holds native ⟨22, by rw [constraint_count]; decide⟩
  have high := assertion_of_holds native ⟨23, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval, environment] at link comparison low high
  have linkEq : w 36 = (1 - w 8) * (w 17 + w 18) := by linear_combination -link
  have comparisonEq : w 37 = (1 - w 8) * (w 19 + w 20) := by linear_combination -comparison
  have lowEq : w 38 = w 26 * w 36 + w 35 * w 37 := by linear_combination -low
  have highEq : w 39 = w 27 * w 36 := by linear_combination -high
  rcases flag with zero | one
  · rw [zero, sub_zero, one_mul] at linkEq comparisonEq
    rcases write_routes (by decide) native mask with route | route | route
    · rw [route.1] at linkEq
      rw [route.2] at comparisonEq
      simp [lowEq, highEq, linkEq, comparisonEq, Word.Bounded, limbBase]
    · rw [route.1] at linkEq
      rw [route.2] at comparisonEq
      rw [lowEq, highEq]
      simpa only [linkEq, comparisonEq, mul_one, mul_zero, add_zero] using
        (show (Word.mk (w 26).val (w 27).val).Bounded from
          ⟨range16_bound (lookup_of_holds native ⟨0, by rw [lookup_count]; decide⟩),
           range16_bound (lookup_of_holds native ⟨1, by rw [lookup_count]; decide⟩)⟩)
    · rw [route.1] at linkEq
      rw [route.2] at comparisonEq
      have control := (fixed_effects native).control
      split_ifs at control with condition
      all_goals simp [lowEq, highEq, linkEq, comparisonEq, control, Word.Bounded, limbBase] <;> decide
  · simp [one, sub_self, zero_mul] at linkEq comparisonEq
    simp [lowEq, highEq, linkEq, comparisonEq, Word.Bounded, limbBase]

end Airbender.JumpBranchSlt.Proofs
