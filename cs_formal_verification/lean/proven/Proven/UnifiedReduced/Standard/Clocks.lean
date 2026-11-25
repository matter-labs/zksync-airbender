module
public import Proven.UnifiedReduced.Standard.Artifact
public import Proven.UnifiedReduced.ArtifactChecks
public import Proven.CircuitField
public import Proven.Trace.Timestamps
public import Mathlib.Tactic.FinCases

@[expose] public section
namespace Airbender.UnifiedReduced.Standard
open Trace Verification
set_option maxRecDepth 8192

theorem clock_equations {p : Nat} [Fact p.Prime] {profile : Profile} {setup} {w : Nat → ZMod p}
    (inverse : (profile.clockInv : ZMod p) * 524288 = 1)
    (square : (profile.clockInv : ZMod p) * profile.clockInv = profile.clockSquare)
    (row : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints profile setup)) :
    ∃ c : Nat, c ≤ 1 ∧ w 2 + 4 = w 32 + 524288 * c ∧ w 3 + c = w 33 := by
  have carry := assertion_of_holds row ⟨89, by rw [constraint_count]; decide⟩
  have high := assertion_of_holds row ⟨90, by rw [constraint_count]; decide⟩
  op_index at carry high
  simp [Expression.eval, environment] at carry high
  let d := w 2 + 4 - w 32
  have opposite : (CircuitField.negInvPow profile.modulus 19 : ZMod p) = -profile.clockInv := by
    simp [Profile.clockInv]
  have boolean : (profile.clockInv * d) * (profile.clockInv * d - 1) = 0 := by
    calc
      _ = (profile.clockInv * profile.clockInv) * d * d - profile.clockInv * d := by ring
      _ = 0 := by rw [square]; dsimp [d]; rw [opposite] at carry; linear_combination carry
  have normalized : profile.clockInv * d + w 3 - w 33 = 0 := by
    dsimp [d]; rw [opposite] at high; linear_combination -high
  exact Arithmetic.increment_carry inverse boolean normalized

theorem final_clock_bound {p : Nat} [Fact p.Prime] {w : Nat → ZMod p}
    (times : FlatOperation.ConstraintsHoldFlat (environment w) importedConstraintsTimestampLookups) :
    (decodeTimestamp w importedConstraintsTraceColumns.finalTime).Bounded := by
  have l := lookup_of_holds times ⟨0, by rw [timestamp_count]; decide⟩
  have h := lookup_of_holds times ⟨1, by rw [timestamp_count]; decide⟩
  op_index at l h
  constructor
  · simpa [Expression.eval, environment, decodeTimestamp, importedConstraintsTraceColumns] using Trace.Proofs.range_bound l
  · simpa [Expression.eval, environment, decodeTimestamp, importedConstraintsTraceColumns] using Trace.Proofs.range_bound h

private theorem port_queries {p : Nat} [Fact p.Prime] {profile : Profile} {setup} {w : Nat → ZMod p}
    (core : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints profile setup))
    (times : FlatOperation.ConstraintsHoldFlat (environment w) importedConstraintsTimestampLookups) :
    ∀ port ∈ importedConstraintsTraceColumns.ports,
      w port.borrow * (w port.borrow - 1) = 0 ∧
      ((w port.previous[0] - w 2 - port.offset + timestampBase * w port.borrow) : ZMod p).val < timestampBase ∧
      ((w port.previous[1] + timestampBase - w port.borrow - w 3) : ZMod p).val < timestampBase := by
  intro port mem
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp mem
  have small : i < 3 := hi
  have bit := assertion_of_holds core ⟨117+i, by rw [constraint_count]; omega⟩
  have lower := lookup_of_holds times ⟨2+2*i, by rw [timestamp_count]; omega⟩
  have upper := lookup_of_holds times ⟨3+2*i, by rw [timestamp_count]; omega⟩
  interval_cases i <;> op_index at bit lower upper <;>
    replace lower := Trace.Proofs.range_bound lower <;>
    replace upper := Trace.Proofs.range_bound upper <;>
    simp [Expression.eval, environment] at lower upper <;>
    refine ⟨?_, ?_, ?_⟩
  all_goals try (solve | simpa [Expression.eval, environment, importedConstraintsTraceColumns, sub_eq_add_neg] using bit)
  · change ((w 34 - w 2 - (0 : Nat) + 524288 * w 123) : ZMod p).val < 524288
    convert lower using 1; congr 1; ring
  · change ((w 35 + 524288 - w 123 - w 3) : ZMod p).val < 524288
    convert upper using 1; congr 1; ring
  · change ((w 40 - w 2 - (1 : Nat) + 524288 * w 124) : ZMod p).val < 524288
    convert lower using 1; congr 1; ring
  · change ((w 41 + 524288 - w 124 - w 3) : ZMod p).val < 524288
    convert upper using 1; congr 1; ring
  · change ((w 46 - w 2 - (2 : Nat) + 524288 * w 125) : ZMod p).val < 524288
    convert lower using 1; congr 1; ring
  · change ((w 47 + 524288 - w 125 - w 3) : ZMod p).val < 524288
    convert upper using 1; congr 1; ring

theorem clock_advance {p : Nat} [Fact p.Prime] {profile : Profile} {setup} {w : Nat → ZMod p}
    (hp : 2 * timestampBase + 4 < p) (inverse : (profile.clockInv : ZMod p) * 524288 = 1)
    (square : (profile.clockInv : ZMod p) * profile.clockInv = profile.clockSquare)
    (row : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints profile setup))
    (times : FlatOperation.ConstraintsHoldFlat (environment w) importedConstraintsTimestampLookups)
    (initial : (decodeTimestamp w importedConstraintsTraceColumns.initialTime).Bounded) :
    (decodeTimestamp w importedConstraintsTraceColumns.finalTime).value =
      (decodeTimestamp w importedConstraintsTraceColumns.initialTime).value + 4 := by
  obtain ⟨c, bit, lo, hi⟩ := clock_equations inverse square row
  apply Trace.Proofs.increment hp initial (final_clock_bound times) bit
  · simpa [decodeTimestamp, importedConstraintsTraceColumns, timestampBase] using lo
  · simpa [decodeTimestamp, importedConstraintsTraceColumns] using hi

theorem clock_accesses {p : Nat} [Fact p.Prime] {profile : Profile} {setup} {w : Nat → ZMod p}
    (hp : 2 * timestampBase + 4 < p) (inverse : (profile.clockInv : ZMod p) * 524288 = 1)
    (square : (profile.clockInv : ZMod p) * profile.clockInv = profile.clockSquare)
    (row : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints profile setup))
    (times : FlatOperation.ConstraintsHoldFlat (environment w) importedConstraintsTimestampLookups)
    (inputs : ClockInputs importedConstraintsTraceColumns w) : ClockEffects importedConstraintsTraceColumns w := by
  apply Trace.Proofs.clock_effects hp inputs (final_clock_bound times) (clock_equations inverse square row)
  · intro port mem
    simp [importedConstraintsTraceColumns] at mem
    rcases mem with rfl | rfl | rfl <;> decide
  · exact port_queries row times

end Airbender.UnifiedReduced.Standard
