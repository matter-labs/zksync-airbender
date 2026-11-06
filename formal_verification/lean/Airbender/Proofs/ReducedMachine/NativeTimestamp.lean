import Airbender.Proofs.ReducedMachine.NativeClockMetadata
import Airbender.Proofs.Constraints
import Airbender.Review.Helpers.Properties
import Airbender.Proofs.Trace.Timestamps

namespace Airbender.ReducedMachine.NativeClockProofs
open Native
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

theorem timestamp_equations {p : Nat} [Fact p.Prime] {w : Nat → ZMod p} {setup : Table (ZMod p) (fields 4)}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup)) :
    ∃ c : Nat, c ≤ 1 ∧ w 2 + 4 = w 15 + 524288 * c ∧ w 3 + c = w 16 := by
  have bit := Verification.assertion_of_holds h ⟨30, by change 30 < 117; decide⟩
  have low := Verification.assertion_of_holds h ⟨115, by change 115 < 117; decide⟩
  have high := Verification.assertion_of_holds h ⟨116, by change 116 < 117; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment] at bit low high
  obtain ⟨c, cb, hc⟩ := Arithmetic.boolean_nat (by convert bit using 1; ring)
  rw [hc] at low high
  refine ⟨c, cb, ?_, ?_⟩
  · linear_combination -low
  · linear_combination -high

theorem final_clock_bound {p : Nat} [Fact p.Prime] {w : Nat → ZMod p} {setup : Table (ZMod p) (fields 4)}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup)) :
    (Trace.decodeTimestamp w importedConstraintsTraceColumns.finalTime).Bounded := by
  have lower := Verification.timestamp19_bound (Verification.lookup_of_holds h
    ⟨8, by change 8 < 22; decide⟩)
  have upper := Verification.timestamp19_bound (Verification.lookup_of_holds h
    ⟨9, by change 9 < 22; decide⟩)
  simp [Expression.eval, Verification.environment] at lower upper
  exact ⟨lower, upper⟩

/-- V2's two separate carry equations need no BabyBear inverse constant. -/
theorem clock_advance {p : Nat} [Fact p.Prime] (hp : 1048580 < p) {w : Nat → ZMod p} {setup : Table (ZMod p) (fields 4)}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (initial : (Trace.decodeTimestamp w importedConstraintsTraceColumns.initialTime).Bounded) :
    (Trace.decodeTimestamp w importedConstraintsTraceColumns.finalTime).value =
      (Trace.decodeTimestamp w importedConstraintsTraceColumns.initialTime).value + 4 := by
  obtain ⟨c, bit, low, high⟩ := timestamp_equations h
  apply Trace.Proofs.increment hp initial (final_clock_bound h) bit
  · simpa [Trace.decodeTimestamp, importedConstraintsTraceColumns] using low
  · simpa [Trace.decodeTimestamp, importedConstraintsTraceColumns] using high

theorem clock_effects {p : Nat} [Fact p.Prime] (hp : 1048580 < p) {w : Nat → ZMod p} {setup : Table (ZMod p) (fields 4)}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (inputs : Trace.ClockInputs importedConstraintsTraceColumns w) :
    Trace.ClockEffects importedConstraintsTraceColumns w := by
  apply Trace.Proofs.clock_effects hp inputs (final_clock_bound h)
    (by simpa [importedConstraintsTraceColumns, Trace.timestampBase] using timestamp_equations h)
  · intro port member
    simp [importedConstraintsTraceColumns] at member
    rcases member with rfl | rfl | rfl <;> decide
  · intro port member
    simp [importedConstraintsTraceColumns] at member
    rcases member with rfl | rfl | rfl
    · simp only [Nat.cast_zero, Nat.cast_ofNat, Trace.timestampBase]
      change w 134 * (w 134 - 1) = 0 ∧
        ((w 132 - w 2 - 0 + 524288 * w 134) : ZMod p).val < 524288 ∧
        ((w 133 + 524288 - w 134 - w 3) : ZMod p).val < 524288
      have bit := Verification.assertion_of_holds h ⟨27, by change 27 < 117; decide⟩
      have lower := Verification.timestamp19_bound (Verification.lookup_of_holds h
        ⟨10, by change 10 < 22; decide⟩)
      have upper := Verification.timestamp19_bound (Verification.lookup_of_holds h
        ⟨11, by change 11 < 22; decide⟩)
      simp [importedConstraints, FlatOperation.constraints, Expression.eval,
        Verification.environment] at bit
      simp [Expression.eval, Verification.environment] at lower upper
      refine ⟨?_, ?_, ?_⟩
      · convert bit using 1; ring
      · convert lower using 1; congr 1; ring
      · convert upper using 1; congr 1; ring
    · simp only [Nat.cast_one, Nat.cast_ofNat, Trace.timestampBase]
      change w 137 * (w 137 - 1) = 0 ∧
        ((w 135 - w 2 - 1 + 524288 * w 137) : ZMod p).val < 524288 ∧
        ((w 136 + 524288 - w 137 - w 3) : ZMod p).val < 524288
      have bit := Verification.assertion_of_holds h ⟨28, by change 28 < 117; decide⟩
      have lower := Verification.timestamp19_bound (Verification.lookup_of_holds h
        ⟨12, by change 12 < 22; decide⟩)
      have upper := Verification.timestamp19_bound (Verification.lookup_of_holds h
        ⟨13, by change 13 < 22; decide⟩)
      simp [importedConstraints, FlatOperation.constraints, Expression.eval,
        Verification.environment] at bit
      simp [Expression.eval, Verification.environment] at lower upper
      refine ⟨?_, ?_, ?_⟩
      · convert bit using 1; ring
      · convert lower using 1; congr 1; ring
      · convert upper using 1; congr 1; ring
    · simp only [Nat.cast_ofNat, Trace.timestampBase]
      change w 140 * (w 140 - 1) = 0 ∧
        ((w 138 - w 2 - 2 + 524288 * w 140) : ZMod p).val < 524288 ∧
        ((w 139 + 524288 - w 140 - w 3) : ZMod p).val < 524288
      have bit := Verification.assertion_of_holds h ⟨29, by change 29 < 117; decide⟩
      have lower := Verification.timestamp19_bound (Verification.lookup_of_holds h
        ⟨14, by change 14 < 22; decide⟩)
      have upper := Verification.timestamp19_bound (Verification.lookup_of_holds h
        ⟨15, by change 15 < 22; decide⟩)
      simp [importedConstraints, FlatOperation.constraints, Expression.eval,
        Verification.environment] at bit
      simp [Expression.eval, Verification.environment] at lower upper
      refine ⟨?_, ?_, ?_⟩
      · convert bit using 1; ring
      · convert lower using 1; congr 1; ring
      · convert upper using 1; congr 1; ring

end Airbender.ReducedMachine.NativeClockProofs
