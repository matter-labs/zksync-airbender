import Airbender.Review.Blake2Round.Artifact
import Airbender.Review.Properties
import Airbender.Proofs.Constraints
import Airbender.Proofs.Arithmetic.Chunks

namespace Airbender.Blake2Round.Proofs

set_option maxRecDepth 16384

/-- The two imported scaled-range queries enforce 128-byte state and 64-byte
    message alignment. No pointer-range or memory-transport premise is used.
    The serialized inverse identity remains an explicit field-compatibility premise. -/
theorem pointer_alignment {p : Nat} [Fact p.Prime] (hp : 8388608 ≤ p)
    (compatible : 128 * (-15728640 : ZMod p) = 1)
    {setup : Table (ZMod p) (fields 4)} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup)) :
    (w 3).val % 128 = 0 ∧ (w 101).val % 64 = 0 := by
  have state := Verification.range16_bound (Verification.lookup_of_holds h ⟨0, by rw [lookup_count]; decide⟩)
  have message := Verification.range16_bound (Verification.lookup_of_holds h ⟨1, by rw [lookup_count]; decide⟩)
  simp [Expression.eval, Verification.environment, Arithmetic.limbBase] at state message
  have messageInverse : 64 * (-31457280 : ZMod p) = 1 := by linear_combination compatible
  have stateValue := Arithmetic.value_of_scaled_range (by omega : 128 * 65536 ≤ p)
    (by decide) compatible (by simpa only [neg_mul] using state)
  have messageValue := Arithmetic.value_of_scaled_range (by omega : 64 * 65536 ≤ p)
    (by decide) messageInverse (by simpa only [neg_mul] using message)
  rw [stateValue, messageValue]
  omega

end Airbender.Blake2Round.Proofs
