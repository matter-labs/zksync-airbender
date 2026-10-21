import Airbender.Proofs.SubwordMemory.ArtifactChecks
import Airbender.Proofs.Constraints
import Airbender.Review.Helpers.Properties
import Airbender.Proofs.Trace.Timestamps

namespace Airbender.SubwordMemory.Proofs
set_option autoImplicit false

theorem timestamp_equations {p : Nat} [Fact p.Prime] {rom : Verification.WordROM} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints rom)) :
    ∃ c : Nat, c ≤ 1 ∧ w 2 + 4 = w 15 + 524288 * c ∧ w 3 + c = w 16 := by
  have bit := Verification.assertion_of_holds h ⟨8, by rw [constraint_count]; decide⟩
  have low := Verification.assertion_of_holds h ⟨49, by rw [constraint_count]; decide⟩
  have high := Verification.assertion_of_holds h ⟨50, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment] at bit low high
  obtain ⟨c, cb, hc⟩ := Arithmetic.boolean_nat (by convert bit using 1; ring)
  rw [hc] at low high
  refine ⟨c, cb, ?_, ?_⟩
  · linear_combination -low
  · linear_combination -high

theorem final_clock_bound {p : Nat} [Fact p.Prime] {rom : Verification.WordROM} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints rom)) :
    (Trace.decodeTimestamp w importedConstraintsTraceColumns.finalTime).Bounded := by
  have lower := Verification.timestamp19_bound (Verification.lookup_of_holds h
    ⟨2, by rw [lookup_count]; decide⟩)
  have upper := Verification.timestamp19_bound (Verification.lookup_of_holds h
    ⟨3, by rw [lookup_count]; decide⟩)
  simp [Expression.eval, Verification.environment] at lower upper
  exact ⟨lower, upper⟩

/-- V2's two separate carry equations need no BabyBear inverse constant. -/
theorem clock_advance {p : Nat} [Fact p.Prime] (hp : 1048580 < p) {rom : Verification.WordROM} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints rom))
    (initial : (Trace.decodeTimestamp w importedConstraintsTraceColumns.initialTime).Bounded) :
    (Trace.decodeTimestamp w importedConstraintsTraceColumns.finalTime).value =
      (Trace.decodeTimestamp w importedConstraintsTraceColumns.initialTime).value + 4 := by
  obtain ⟨c, bit, low, high⟩ := timestamp_equations h
  apply Trace.Proofs.increment hp initial (final_clock_bound h) bit
  · simpa [Trace.decodeTimestamp, importedConstraintsTraceColumns] using low
  · simpa [Trace.decodeTimestamp, importedConstraintsTraceColumns] using high

theorem clock_effects {p : Nat} [Fact p.Prime] (hp : 1048580 < p) {rom : Verification.WordROM} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints rom))
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
      change w 70 * (w 70 - 1) = 0 ∧
        ((w 68 - w 2 - 0 + 524288 * w 70) : ZMod p).val < 524288 ∧
        ((w 69 + 524288 - w 70 - w 3) : ZMod p).val < 524288
      have bit := Verification.assertion_of_holds h ⟨5, by rw [constraint_count]; decide⟩
      have lower := Verification.timestamp19_bound (Verification.lookup_of_holds h
        ⟨4, by rw [lookup_count]; decide⟩)
      have upper := Verification.timestamp19_bound (Verification.lookup_of_holds h
        ⟨5, by rw [lookup_count]; decide⟩)
      simp [importedConstraints, FlatOperation.constraints, Expression.eval,
        Verification.environment] at bit
      simp [Expression.eval, Verification.environment] at lower upper
      refine ⟨?_, ?_, ?_⟩
      · convert bit using 1; ring
      · convert lower using 1; congr 1; ring
      · convert upper using 1; congr 1; ring
    · simp only [Nat.cast_one, Nat.cast_ofNat, Trace.timestampBase]
      change w 73 * (w 73 - 1) = 0 ∧
        ((w 71 - w 2 - 1 + 524288 * w 73) : ZMod p).val < 524288 ∧
        ((w 72 + 524288 - w 73 - w 3) : ZMod p).val < 524288
      have bit := Verification.assertion_of_holds h ⟨6, by rw [constraint_count]; decide⟩
      have lower := Verification.timestamp19_bound (Verification.lookup_of_holds h
        ⟨6, by rw [lookup_count]; decide⟩)
      have upper := Verification.timestamp19_bound (Verification.lookup_of_holds h
        ⟨7, by rw [lookup_count]; decide⟩)
      simp [importedConstraints, FlatOperation.constraints, Expression.eval,
        Verification.environment] at bit
      simp [Expression.eval, Verification.environment] at lower upper
      refine ⟨?_, ?_, ?_⟩
      · convert bit using 1; ring
      · convert lower using 1; congr 1; ring
      · convert upper using 1; congr 1; ring
    · simp only [Nat.cast_ofNat, Trace.timestampBase]
      change w 76 * (w 76 - 1) = 0 ∧
        ((w 74 - w 2 - 2 + 524288 * w 76) : ZMod p).val < 524288 ∧
        ((w 75 + 524288 - w 76 - w 3) : ZMod p).val < 524288
      have bit := Verification.assertion_of_holds h ⟨7, by rw [constraint_count]; decide⟩
      have lower := Verification.timestamp19_bound (Verification.lookup_of_holds h
        ⟨8, by rw [lookup_count]; decide⟩)
      have upper := Verification.timestamp19_bound (Verification.lookup_of_holds h
        ⟨9, by rw [lookup_count]; decide⟩)
      simp [importedConstraints, FlatOperation.constraints, Expression.eval,
        Verification.environment] at bit
      simp [Expression.eval, Verification.environment] at lower upper
      refine ⟨?_, ?_, ?_⟩
      · convert bit using 1; ring
      · convert lower using 1; congr 1; ring
      · convert upper using 1; congr 1; ring

end Airbender.SubwordMemory.Proofs
