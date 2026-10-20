import Human.Circuits.UnifiedReduced.Artifact
import Human.Helpers.Properties
import Slop.Constraints
import Slop.Trace.Timestamps

namespace Airbender.UnifiedReduced.Proofs
open Trace

theorem timestamp_equations {p : Nat} [Fact p.Prime]
    (inverse : (-3840 : ZMod p) * 524288 = 1) {setup : Table (ZMod p) (fields 10)} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup)) :
    ∃ carry : Nat, carry ≤ 1 ∧ w 2 + 4 = w 32 + 524288 * carry ∧ w 3 + carry = w 33 := by
  have carry := Verification.assertion_of_holds h
    ⟨93, by simp [importedConstraints, FlatOperation.constraints]⟩
  have high := Verification.assertion_of_holds h
    ⟨94, by simp [importedConstraints, FlatOperation.constraints]⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment] at carry high
  have boolean : (-3840 * (w 2 + 4 - w 32)) *
      (-3840 * (w 2 + 4 - w 32) - 1) = 0 := by
    convert carry using 1
    ring
  have normalized : -3840 * (w 2 + 4 - w 32) + w 3 - w 33 = 0 := by
    linear_combination -high
  exact Arithmetic.increment_carry inverse boolean normalized

theorem final_clock_bound {p : Nat} [Fact p.Prime] {setup : Table (ZMod p) (fields 10)} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (clockConstraints setup)) :
    (decodeTimestamp w importedConstraintsTraceColumns.finalTime).Bounded := by
  have timestamps := Verification.holds_of_sublist h
    (List.sublist_append_right (importedConstraints setup) importedConstraintsTimestampLookups)
  have low := Trace.Proofs.range_bound (Verification.lookup_of_holds timestamps
    ⟨0, by simp [importedConstraintsTimestampLookups, FlatOperation.lookups]⟩)
  have high := Trace.Proofs.range_bound (Verification.lookup_of_holds timestamps
    ⟨1, by simp [importedConstraintsTimestampLookups, FlatOperation.lookups]⟩)
  simp [Expression.eval, Verification.environment] at low high
  exact ⟨low, high⟩

theorem clock_advance {p : Nat} [Fact p.Prime]
    (hp : 2 * timestampBase + 4 < p) (inverse : (-3840 : ZMod p) * 524288 = 1)
    {setup : Table (ZMod p) (fields 10)} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (clockConstraints setup))
    (initial : (decodeTimestamp w importedConstraintsTraceColumns.initialTime).Bounded) :
    (decodeTimestamp w importedConstraintsTraceColumns.finalTime).value =
      (decodeTimestamp w importedConstraintsTraceColumns.initialTime).value + 4 := by
  have core := Verification.holds_of_sublist h
    (List.sublist_append_left (importedConstraints setup) importedConstraintsTimestampLookups)
  obtain ⟨carry, bound, low, high⟩ := timestamp_equations inverse core
  apply Trace.Proofs.increment hp initial (final_clock_bound h) bound
  · simpa [decodeTimestamp, importedConstraintsTraceColumns, timestampBase] using low
  · simpa [decodeTimestamp, importedConstraintsTraceColumns] using high

theorem clocks {p : Nat} [Fact p.Prime]
    (hp : 2 * timestampBase + 4 < p) (inverse : (-3840 : ZMod p) * 524288 = 1)
    {setup : Table (ZMod p) (fields 10)} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (clockConstraints setup))
    (inputs : ClockInputs importedConstraintsTraceColumns w) :
    ClockEffects importedConstraintsTraceColumns w := by
  have core := Verification.holds_of_sublist h
    (List.sublist_append_left (importedConstraints setup) importedConstraintsTimestampLookups)
  have timestamps := Verification.holds_of_sublist h
    (List.sublist_append_right (importedConstraints setup) importedConstraintsTimestampLookups)
  apply Trace.Proofs.clock_effects hp inputs (final_clock_bound h)
    (by simpa [importedConstraintsTraceColumns, timestampBase] using timestamp_equations inverse core)
  · intro port member
    simp [importedConstraintsTraceColumns] at member
    rcases member with rfl | rfl | rfl <;> decide
  · intro port member
    simp [importedConstraintsTraceColumns] at member
    rcases member with rfl | rfl | rfl
    · have bit := Verification.assertion_of_holds core
        ⟨126, by simp [importedConstraints, FlatOperation.constraints]⟩
      have lower := Trace.Proofs.range_bound (Verification.lookup_of_holds timestamps
        ⟨2, by simp [importedConstraintsTimestampLookups, FlatOperation.lookups]⟩)
      have upper := Trace.Proofs.range_bound (Verification.lookup_of_holds timestamps
        ⟨3, by simp [importedConstraintsTimestampLookups, FlatOperation.lookups]⟩)
      simp [Expression.eval, Verification.environment] at lower upper
      refine ⟨?_, ?_, ?_⟩
      · simpa [importedConstraints, FlatOperation.constraints, Expression.eval,
          Verification.environment, sub_eq_add_neg] using bit
      · change ((w 34 - w 2 - (0 : Nat) + timestampBase * w 131) : ZMod p).val < timestampBase
        convert lower using 1; congr 1; ring
      · change ((w 35 + timestampBase - w 131 - w 3) : ZMod p).val < timestampBase
        convert upper using 1; congr 1; ring
    · have bit := Verification.assertion_of_holds core
        ⟨127, by simp [importedConstraints, FlatOperation.constraints]⟩
      have lower := Trace.Proofs.range_bound (Verification.lookup_of_holds timestamps
        ⟨4, by simp [importedConstraintsTimestampLookups, FlatOperation.lookups]⟩)
      have upper := Trace.Proofs.range_bound (Verification.lookup_of_holds timestamps
        ⟨5, by simp [importedConstraintsTimestampLookups, FlatOperation.lookups]⟩)
      simp [Expression.eval, Verification.environment] at lower upper
      refine ⟨?_, ?_, ?_⟩
      · simpa [importedConstraints, FlatOperation.constraints, Expression.eval,
          Verification.environment, sub_eq_add_neg] using bit
      · change ((w 40 - w 2 - (1 : Nat) + timestampBase * w 132) : ZMod p).val < timestampBase
        convert lower using 1; congr 1; ring
      · change ((w 41 + timestampBase - w 132 - w 3) : ZMod p).val < timestampBase
        convert upper using 1; congr 1; ring
    · have bit := Verification.assertion_of_holds core
        ⟨128, by simp [importedConstraints, FlatOperation.constraints]⟩
      have lower := Trace.Proofs.range_bound (Verification.lookup_of_holds timestamps
        ⟨6, by simp [importedConstraintsTimestampLookups, FlatOperation.lookups]⟩)
      have upper := Trace.Proofs.range_bound (Verification.lookup_of_holds timestamps
        ⟨7, by simp [importedConstraintsTimestampLookups, FlatOperation.lookups]⟩)
      simp [Expression.eval, Verification.environment] at lower upper
      refine ⟨?_, ?_, ?_⟩
      · simpa [importedConstraints, FlatOperation.constraints, Expression.eval,
          Verification.environment, sub_eq_add_neg] using bit
      · change ((w 46 - w 2 - (2 : Nat) + timestampBase * w 133) : ZMod p).val < timestampBase
        convert lower using 1; congr 1; ring
      · change ((w 47 + timestampBase - w 133 - w 3) : ZMod p).val < timestampBase
        convert upper using 1; congr 1; ring

end Airbender.UnifiedReduced.Proofs
