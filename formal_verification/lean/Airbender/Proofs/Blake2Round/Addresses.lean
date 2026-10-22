import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Review.Helpers.Core.SerializedInverse
import Airbender.Proofs.Blake2Round.ArtifactChecks
import Airbender.Review.Circuits.Blake2Round.Artifact
import Airbender.Review.Helpers.Properties
import Airbender.Proofs.Constraints
import Airbender.Proofs.Arithmetic.Chunks
import Airbender.Proofs.BabyBear
import Airbender.Proofs.Trace.Timestamps
import Mathlib.Tactic.LinearCombination

namespace Airbender.Blake2Round.Proofs

set_option maxRecDepth 16384

/-- The two imported scaled-range queries enforce 128-byte state and 64-byte
    message alignment. No pointer-range or memory-transport premise is used.
    The serialized inverse identity remains an explicit field-compatibility premise. -/
theorem pointer_alignment {p : Nat} [Fact p.Prime] (_hp : FieldCapacity.NativeHashCapacity p)
    (compatible : SerializedInverse.Scale128 p)
    {setup : Table (ZMod p) (fields 6)} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup)) :
    (w 3).val % 128 = 0 ∧ (w 101).val % 64 = 0 := by
  have characteristic : (babyBearModulus : ZMod p) = 0 := by
    unfold babyBearModulus
    linear_combination -compatible
  have field := babyBear_eq_of_natCast_zero characteristic
  have state := Trace.Proofs.range_bound (Verification.lookup_of_holds h ⟨0, by rw [lookup_count]; decide⟩)
  have message := Trace.Proofs.range_bound (Verification.lookup_of_holds h ⟨1, by rw [lookup_count]; decide⟩)
  simp [Expression.eval, Verification.environment] at state message
  have messageInverse : SerializedInverse.Scale64 p := by linear_combination compatible
  have stateValue := Arithmetic.value_of_scaled_range (by rw [field]; decide : 128 * Trace.timestampBase ≤ p)
    (by decide) compatible (by simpa only [neg_mul] using state)
  have messageValue := Arithmetic.value_of_scaled_range (by rw [field]; decide : 64 * Trace.timestampBase ≤ p)
    (by decide) messageInverse (by simpa only [neg_mul] using message)
  rw [stateValue, messageValue]
  omega

end Airbender.Blake2Round.Proofs
