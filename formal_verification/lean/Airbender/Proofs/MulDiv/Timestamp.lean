import Airbender.Review.MulDiv.Artifact
import Airbender.Review.Properties
import Airbender.Proofs.Constraints
import Airbender.Proofs.Trace.Timestamps

namespace Airbender.MulDiv.Proofs
open Trace

theorem timestamp_equations {p : Nat} [Fact p.Prime]
    (inverse : (-3840 : ZMod p) * 524288 = 1) {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints) :
    ∃ carry : Nat, carry ≤ 1 ∧ w 2 + 4 = w 16 + 524288 * carry ∧ w 3 + carry = w 17 := by
  have carry := Verification.assertion_of_holds h
    ⟨34, by simp [importedConstraints, FlatOperation.constraints]⟩
  have high := Verification.assertion_of_holds h
    ⟨35, by simp [importedConstraints, FlatOperation.constraints]⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment] at carry high
  have boolean : (-3840 * (w 2 + 4 - w 16)) *
      (-3840 * (w 2 + 4 - w 16) - 1) = 0 := by
    convert carry using 1
    ring
  have normalized : -3840 * (w 2 + 4 - w 16) + w 3 - w 17 = 0 := by
    linear_combination -high
  exact Arithmetic.increment_carry inverse boolean normalized

theorem final_clock_bound {p : Nat} [Fact p.Prime] {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) clockConstraints) :
    (decodeTimestamp w importedConstraintsTraceColumns.finalTime).Bounded := by
  have timestamps := Verification.holds_of_sublist h
    (List.sublist_append_right importedConstraints importedConstraintsTimestampLookups)
  have low := Trace.Proofs.range_bound (Verification.lookup_of_holds timestamps
    ⟨0, by simp [importedConstraintsTimestampLookups, FlatOperation.lookups]⟩)
  have high := Trace.Proofs.range_bound (Verification.lookup_of_holds timestamps
    ⟨1, by simp [importedConstraintsTimestampLookups, FlatOperation.lookups]⟩)
  simp [Expression.eval, Verification.environment] at low high
  exact ⟨low, high⟩

/-- Native clock advancement and all three strict prior-write comparisons,
    independent of the selected unsigned multiply/divide mode. Global histories will supply
    `ClockInputs`; no per-read or expected execution value occurs here. -/
theorem clocks {p : Nat} [Fact p.Prime]
    (hp : 2 * timestampBase + 4 < p) (inverse : (-3840 : ZMod p) * 524288 = 1)
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) clockConstraints)
    (inputs : ClockInputs importedConstraintsTraceColumns w) :
    ClockEffects importedConstraintsTraceColumns w := by
  have core := Verification.holds_of_sublist h
    (List.sublist_append_left importedConstraints importedConstraintsTimestampLookups)
  have timestamps := Verification.holds_of_sublist h
    (List.sublist_append_right importedConstraints importedConstraintsTimestampLookups)
  apply Trace.Proofs.clock_effects hp inputs (final_clock_bound h)
    (by simpa [importedConstraintsTraceColumns, timestampBase] using timestamp_equations inverse core)
  · intro port member
    simp [importedConstraintsTraceColumns] at member
    rcases member with rfl | rfl | rfl <;> decide
  · intro port member
    simp [importedConstraintsTraceColumns] at member
    rcases member with rfl | rfl | rfl
    · have bit := Verification.assertion_of_holds core
        ⟨40, by simp [importedConstraints, FlatOperation.constraints]⟩
      have lower := Trace.Proofs.range_bound (Verification.lookup_of_holds timestamps
        ⟨2, by simp [importedConstraintsTimestampLookups, FlatOperation.lookups]⟩)
      have upper := Trace.Proofs.range_bound (Verification.lookup_of_holds timestamps
        ⟨3, by simp [importedConstraintsTimestampLookups, FlatOperation.lookups]⟩)
      simp [Expression.eval, Verification.environment] at lower upper
      refine ⟨?_, ?_, ?_⟩
      · simpa [importedConstraints, FlatOperation.constraints, Expression.eval,
          Verification.environment, sub_eq_add_neg] using bit
      · change ((w 18 - w 2 - (0 : Nat) + timestampBase * w 65) : ZMod p).val < timestampBase
        convert lower using 1; congr 1; ring
      · change ((w 19 + timestampBase - w 65 - w 3) : ZMod p).val < timestampBase
        convert upper using 1; congr 1; ring
    · have bit := Verification.assertion_of_holds core
        ⟨41, by simp [importedConstraints, FlatOperation.constraints]⟩
      have lower := Trace.Proofs.range_bound (Verification.lookup_of_holds timestamps
        ⟨4, by simp [importedConstraintsTimestampLookups, FlatOperation.lookups]⟩)
      have upper := Trace.Proofs.range_bound (Verification.lookup_of_holds timestamps
        ⟨5, by simp [importedConstraintsTimestampLookups, FlatOperation.lookups]⟩)
      simp [Expression.eval, Verification.environment] at lower upper
      refine ⟨?_, ?_, ?_⟩
      · simpa [importedConstraints, FlatOperation.constraints, Expression.eval,
          Verification.environment, sub_eq_add_neg] using bit
      · change ((w 22 - w 2 - (1 : Nat) + timestampBase * w 66) : ZMod p).val < timestampBase
        convert lower using 1; congr 1; ring
      · change ((w 23 + timestampBase - w 66 - w 3) : ZMod p).val < timestampBase
        convert upper using 1; congr 1; ring
    · have bit := Verification.assertion_of_holds core
        ⟨42, by simp [importedConstraints, FlatOperation.constraints]⟩
      have lower := Trace.Proofs.range_bound (Verification.lookup_of_holds timestamps
        ⟨6, by simp [importedConstraintsTimestampLookups, FlatOperation.lookups]⟩)
      have upper := Trace.Proofs.range_bound (Verification.lookup_of_holds timestamps
        ⟨7, by simp [importedConstraintsTimestampLookups, FlatOperation.lookups]⟩)
      simp [Expression.eval, Verification.environment] at lower upper
      refine ⟨?_, ?_, ?_⟩
      · simpa [importedConstraints, FlatOperation.constraints, Expression.eval,
          Verification.environment, sub_eq_add_neg] using bit
      · change ((w 30 - w 2 - (2 : Nat) + timestampBase * w 67) : ZMod p).val < timestampBase
        convert lower using 1; congr 1; ring
      · change ((w 31 + timestampBase - w 67 - w 3) : ZMod p).val < timestampBase
        convert upper using 1; congr 1; ring

end Airbender.MulDiv.Proofs
