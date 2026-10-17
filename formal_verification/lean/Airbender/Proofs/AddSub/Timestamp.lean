import Airbender.Proofs.AddSub.ArtifactChecks
import Airbender.Proofs.Constraints
import Airbender.Review.Helpers.Properties
import Airbender.Proofs.Trace.Timestamps

namespace Airbender.AddSub.Proofs

theorem timestamp_equations {p : Nat} [Fact p.Prime] {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints) :
    ∃ c : Nat, c ≤ 1 ∧ w 2 + 4 = w 15 + 524288 * c ∧ w 3 + c = w 16 := by
  have bit := Verification.assertion_of_holds h ⟨15, by rw [constraint_count]; decide⟩
  have low := Verification.assertion_of_holds h ⟨35, by rw [constraint_count]; decide⟩
  have high := Verification.assertion_of_holds h ⟨36, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment] at bit low high
  obtain ⟨c, cb, hc⟩ := Arithmetic.boolean_nat (by convert bit using 1; ring)
  rw [hc] at low high
  refine ⟨c, cb, ?_, ?_⟩
  · linear_combination -low
  · linear_combination -high

theorem clock_effects {p : Nat} [Fact p.Prime] (hp : 1048580 < p) {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (inputs : Trace.ClockInputs importedConstraintsTraceColumns w) :
    Trace.ClockEffects importedConstraintsTraceColumns w := by
  have lower := Verification.timestamp19_bound (Verification.lookup_of_holds h
    ⟨4, by rw [lookup_count]; decide⟩)
  have upper := Verification.timestamp19_bound (Verification.lookup_of_holds h
    ⟨5, by rw [lookup_count]; decide⟩)
  simp [Expression.eval, Verification.environment] at lower upper
  have finalBounds : (Trace.decodeTimestamp w importedConstraintsTraceColumns.finalTime).Bounded :=
    ⟨lower, upper⟩
  apply Trace.Proofs.clock_effects hp inputs finalBounds
    (by simpa [importedConstraintsTraceColumns, Trace.timestampBase] using timestamp_equations h)
  · intro port member
    simp [importedConstraintsTraceColumns] at member
    rcases member with rfl | rfl | rfl <;> decide
  · intro port member
    simp [importedConstraintsTraceColumns] at member
    rcases member with rfl | rfl | rfl
    · simp only [Nat.cast_zero, Nat.cast_ofNat, Trace.timestampBase]
      change w 46 * (w 46 - 1) = 0 ∧
        ((w 44 - w 2 - 0 + 524288 * w 46) : ZMod p).val < 524288 ∧
        ((w 45 + 524288 - w 46 - w 3) : ZMod p).val < 524288
      have bit := Verification.assertion_of_holds h ⟨12, by rw [constraint_count]; decide⟩
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
    · simp only [Nat.cast_one, Nat.cast_ofNat, Trace.timestampBase]
      change w 49 * (w 49 - 1) = 0 ∧
        ((w 47 - w 2 - 1 + 524288 * w 49) : ZMod p).val < 524288 ∧
        ((w 48 + 524288 - w 49 - w 3) : ZMod p).val < 524288
      have bit := Verification.assertion_of_holds h ⟨13, by rw [constraint_count]; decide⟩
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
    · simp only [Nat.cast_ofNat, Trace.timestampBase]
      change w 52 * (w 52 - 1) = 0 ∧
        ((w 50 - w 2 - 2 + 524288 * w 52) : ZMod p).val < 524288 ∧
        ((w 51 + 524288 - w 52 - w 3) : ZMod p).val < 524288
      have bit := Verification.assertion_of_holds h ⟨14, by rw [constraint_count]; decide⟩
      have lower := Verification.timestamp19_bound (Verification.lookup_of_holds h
        ⟨10, by rw [lookup_count]; decide⟩)
      have upper := Verification.timestamp19_bound (Verification.lookup_of_holds h
        ⟨11, by rw [lookup_count]; decide⟩)
      simp [importedConstraints, FlatOperation.constraints, Expression.eval,
        Verification.environment] at bit
      simp [Expression.eval, Verification.environment] at lower upper
      refine ⟨?_, ?_, ?_⟩
      · convert bit using 1; ring
      · convert lower using 1; congr 1; ring
      · convert upper using 1; congr 1; ring

end Airbender.AddSub.Proofs
