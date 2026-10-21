import Airbender.Review.Circuits.Blake2G.Artifact
import Airbender.Review.Helpers.Properties
import Airbender.Proofs.Constraints
import Airbender.Proofs.Arithmetic.Chunks
import Airbender.Proofs.Blake2G.Lookups
import Airbender.Proofs.BabyBear
import Airbender.Proofs.Trace.Timestamps
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

namespace Airbender.Blake2G.Proofs

set_option maxHeartbeats 800000

/-- Carries, timestamp borrows and execute are forced to be Boolean by the artifact. -/
theorem local_flags {p : Nat} [Fact p.Prime] {setup : Table (ZMod p) (fields 9)}
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup)) :
    ∀ i : Fin 22,
      w Variables.booleanColumns[i] = 0 ∨ w Variables.booleanColumns[i] = 1 := by
  intro i
  have flag := Verification.assertion_of_holds h
    ⟨(#v[0, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31][i]),
      by rw [constraint_count]; fin_cases i <;> decide⟩
  fin_cases i <;> simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment, Variables.booleanColumns,
    mul_eq_zero, ← sub_eq_add_neg, sub_eq_zero, or_comm] at flag ⊢
  all_goals exact flag

/-- The control register is explicitly confined to its low limb, on reads and writes. -/
theorem control_high_zero {p : Nat} [Fact p.Prime] {setup : Table (ZMod p) (fields 9)}
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup)) :
    w Variables.controlReadHi = 0 ∧ w Variables.controlWriteHi = 0 := by
  have read := Verification.assertion_of_holds h ⟨1, by rw [constraint_count]; decide⟩
  have write := Verification.assertion_of_holds h ⟨2, by rw [constraint_count]; decide⟩
  simpa [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment] using And.intro read write

private theorem aligned_of_scaled_bound {p : Nat} [Fact p.Prime] (_hp : 4194304 ≤ p)
    {x : ZMod p} (inverse : 64 * (-31457280 : ZMod p) = 1)
    (bound : ((-31457280 : ZMod p) * x).val < Trace.timestampBase) : x.val % 64 = 0 := by
  have characteristic : (babyBearModulus : ZMod p) = 0 := by
    unfold babyBearModulus
    linear_combination -inverse
  have field := babyBear_eq_of_natCast_zero characteristic
  have value := Arithmetic.value_of_scaled_range
    (by rw [field]; decide : 64 * Trace.timestampBase ≤ p) (by decide) inverse bound
  rw [value]
  simp

/-- The two imported scaled-range queries force both ABI pointers to be 64-byte aligned.
    The serialized inverse identity is an artifact/field compatibility premise. -/
theorem pointer_alignment {p : Nat} [Fact p.Prime] (hp : 4194304 ≤ p)
    (inverse : 64 * (-31457280 : ZMod p) = 1)
    {setup : Table (ZMod p) (fields 9)} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup)) :
    (w Variables.statePointerLo).val % 64 = 0 ∧
      (w Variables.messagePointerLo).val % 64 = 0 := by
  have state := Trace.Proofs.range_bound (Verification.lookup_of_holds h ⟨0, by rw [lookup_count]; decide⟩)
  have message := Trace.Proofs.range_bound (Verification.lookup_of_holds h ⟨1, by rw [lookup_count]; decide⟩)
  simp [Expression.eval,
    Verification.environment] at state message
  exact ⟨aligned_of_scaled_bound hp inverse (by simpa only [neg_mul] using state),
    aligned_of_scaled_bound hp inverse (by simpa only [neg_mul] using message)⟩

end Airbender.Blake2G.Proofs
