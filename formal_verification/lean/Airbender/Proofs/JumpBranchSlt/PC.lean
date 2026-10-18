import Airbender.Proofs.JumpBranchSlt.Selectors
import Airbender.Proofs.JumpBranchSlt.Queries

namespace Airbender.JumpBranchSlt.Proofs
open Verification

variable {w : Nat → ZMod mersenne31Modulus}

/-- This is the actual sixth scalar query, on the candidate high PC limb. -/
theorem candidate_high_bound
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) importedConstraints) :
    (w 43).val < 65536 :=
  range16_bound (lookup_of_holds holds ⟨5, by rw [lookup_count]; decide⟩)

theorem pc_columns
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) importedConstraints)
    (mask : (w 12).val ∈ [1, 2, 4, 8, 16]) :
    (w 13 = w 42 ∨ w 13 = w 48) ∧ w 14 = w 43 := by
  obtain ⟨total, pair, triple⟩ := selector_partition (by decide) holds mask
  have notTaken := assertion_of_holds holds ⟨24, by rw [constraint_count]; decide⟩
  have taken := assertion_of_holds holds ⟨25, by rw [constraint_count]; decide⟩
  have low := assertion_of_holds holds ⟨27, by rw [constraint_count]; decide⟩
  have high := assertion_of_holds holds ⟨28, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    environment] at notTaken taken low high
  have branch : w 45 + w 46 = w 21 := by linear_combination -notTaken - taken
  have highEq : w 14 = w 43 := by
    linear_combination -high + w 43 * (total + branch)
  have route : w 17 + w 18 + w 46 = 0 ∨ w 17 + w 18 + w 46 = 1 := by
    have flag := (fixed_effects holds).control
    split_ifs at flag with condition
    · have eq : w 46 = w 21 := by rw [flag] at taken; linear_combination -taken
      simpa only [eq] using triple
    · have eq : w 46 = 0 := by rw [flag] at taken; linear_combination -taken
      simpa only [eq, add_zero] using pair
  refine ⟨?_, highEq⟩
  rcases route with raw | cleaned
  · left
    linear_combination -low + w 42 * (total + branch) + (w 48 - w 42) * raw
  · right
    linear_combination -low + w 42 * (total + branch) + (w 48 - w 42) * cleaned

theorem pc_bounds
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) importedConstraints)
    (mask : (w 12).val ∈ [1, 2, 4, 8, 16]) :
    (w 13).val < 65536 ∧ (w 14).val < 65536 := by
  have effects := fixed_effects holds
  have high := candidate_high_bound holds
  obtain ⟨lowEq, highEq⟩ := pc_columns holds mask
  refine ⟨?_, by simpa only [highEq] using high⟩
  rcases lowEq with raw | cleaned
  · simpa only [raw] using effects.cleanupBound
  · rw [cleaned, effects.cleaned]
    have bounded : 4 * ((w 42).val / 4) < 65536 := by
      have := effects.cleanupBound
      omega
    rw [ZMod.val_natCast_of_lt (Nat.lt_trans bounded (by decide : 65536 < mersenne31Modulus))]
    exact bounded

end Airbender.JumpBranchSlt.Proofs
