module
public import Slop.Blake2Round.ArtifactChecks
public import Slop.Blake2Round.OpIndex
public import Human.Circuits.Blake2Round.Artifact
public import Human.Helpers.Properties
public import Slop.Constraints
public import Slop.Arithmetic.Chunks
public import Slop.Trace.Timestamps
public import Human.Helpers.Core.BabyBearPrime

@[expose] public section

namespace Airbender.Blake2Round.Proofs

/-- The serialized inverse of 128 belongs to BabyBear: it fixes the field. -/
theorem scale128_field {p : Nat} [Fact p.Prime]
    (compatible : 128 * (-15728640 : ZMod p) = 1) : p = babyBearModulus := by
  have characteristic : (babyBearModulus : ZMod p) = 0 := by
    unfold babyBearModulus
    linear_combination -compatible
  have divisor : p ∣ babyBearModulus := (ZMod.natCast_eq_zero_iff _ _).mp characteristic
  exact ((Nat.dvd_prime babyBearPrime.out).mp divisor).resolve_left
    (Nat.Prime.ne_one (Fact.out : p.Prime))

/-- The two imported scaled timestamp-range queries enforce 128-byte state and
    64-byte message alignment. No pointer-range or memory-transport premise is used.
    The serialized inverse identity remains an explicit field-compatibility premise. -/
theorem pointer_alignment {p : Nat} [Fact p.Prime] (_hp : 8388608 ≤ p)
    (compatible : 128 * (-15728640 : ZMod p) = 1)
    {setup : Table (ZMod p) (fields 6)} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup)) :
    (w 3).val % 128 = 0 ∧ (w 101).val % 64 = 0 := by
  have field := scale128_field compatible
  have stateQuery := Verification.lookup_of_holds h ⟨0, by rw [lookup_count]; decide⟩
  have messageQuery := Verification.lookup_of_holds h ⟨1, by rw [lookup_count]; decide⟩
  op_index at stateQuery messageQuery
  have state := Trace.Proofs.range_bound stateQuery
  have message := Trace.Proofs.range_bound messageQuery
  simp [Expression.eval, Verification.environment] at state message
  have messageInverse : 64 * (-31457280 : ZMod p) = 1 := by linear_combination compatible
  have stateValue := Arithmetic.value_of_scaled_range
    (by rw [field]; decide : 128 * Trace.timestampBase ≤ p)
    (by decide) compatible (by simpa only [neg_mul] using state)
  have messageValue := Arithmetic.value_of_scaled_range
    (by rw [field]; decide : 64 * Trace.timestampBase ≤ p)
    (by decide) messageInverse (by simpa only [neg_mul] using message)
  rw [stateValue, messageValue]
  omega

end Airbender.Blake2Round.Proofs
