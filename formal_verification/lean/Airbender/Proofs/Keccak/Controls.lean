import Airbender.Review.Keccak.Controls
import Airbender.Proofs.Constraints
import Airbender.Proofs.Arithmetic.Chunks
import Airbender.Proofs.Arithmetic.OneHot
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

namespace Airbender.Keccak.Proofs
open Arithmetic
open scoped BigOperators
set_option warningAsError true
set_option maxHeartbeats 800000
set_option maxRecDepth 16384

variable {p : Nat} [Fact p.Prime] {setup : Table (ZMod p) (fields 8)} {w : Nat → ZMod p}

/-- The logical flags are constrained by actual imported equations, rather than
    by the witness generator or the fixed-table interface. -/
theorem control_bits
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup)) :
    (w 0 = 0 ∨ w 0 = 1) ∧ ∀ i : Fin 17, w (63 + i.val) = 0 ∨ w (63 + i.val) = 1 := by
  constructor
  · have flag := Verification.assertion_of_holds h ⟨0, by rw [constraint_count]; decide⟩
    simpa [importedConstraints, FlatOperation.constraints, Expression.eval,
      Verification.environment, mul_eq_zero, ← sub_eq_add_neg, sub_eq_zero, or_comm] using flag
  · intro i
    have flag := Verification.assertion_of_holds h ⟨156 + i.val, by rw [constraint_count]; omega⟩
    fin_cases i <;> simp [importedConstraints, FlatOperation.constraints, Expression.eval,
      Verification.environment, mul_eq_zero, ← sub_eq_add_neg, sub_eq_zero] at flag ⊢
    all_goals exact flag

theorem control_high_zero
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup)) :
    w 4 = 0 ∧ w 6 = 0 := by
  have read := Verification.assertion_of_holds h ⟨1, by rw [constraint_count]; decide⟩
  have write := Verification.assertion_of_holds h ⟨2, by rw [constraint_count]; decide⟩
  simpa [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment] using And.intro read write

private theorem counts_field
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup)) :
    (∑ i : Fin 7, w Variables.modeColumns[i]) = w 0 ∧
    (∑ i : Fin 5, w Variables.iterationColumns[i]) = w 0 := by
  have activeMode := Verification.assertion_of_holds h ⟨4, by rw [constraint_count]; decide⟩
  have activeIteration := Verification.assertion_of_holds h ⟨5, by rw [constraint_count]; decide⟩
  have inactiveMode := Verification.assertion_of_holds h ⟨6, by rw [constraint_count]; decide⟩
  have inactiveIteration := Verification.assertion_of_holds h ⟨7, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment] at activeMode activeIteration inactiveMode inactiveIteration
  simp [Variables.modeColumns, Variables.iterationColumns, Fin.sum_univ_succ]
  rcases (control_bits h).1 with zero | one
  · simp [zero] at inactiveMode inactiveIteration
    simp only [zero]
    constructor
    · linear_combination inactiveMode
    · linear_combination inactiveIteration
  · simp [one] at activeMode activeIteration
    simp only [one]
    constructor
    · linear_combination activeMode
    · linear_combination activeIteration

private theorem count_value {n : Nat} (hn : n < p) {bits : Fin n → ZMod p}
    (boolean : ∀ i, bits i = 0 ∨ bits i = 1) (sum : (∑ i, bits i) = w 0) :
    (∑ i, (bits i).val) = (w 0).val := by
  have bounded : (∑ i, (bits i).val) ≤ n := by
    calc
      _ ≤ ∑ _i : Fin n, 1 := Finset.sum_le_sum (fun i _ => boolean_val (boolean i))
      _ = n := by simp
  apply bounded_nat_eq (F := ZMod p) (p := p) (by omega) (ZMod.val_lt _)
  simpa only [Nat.cast_sum, ZMod.natCast_zmod_val] using sum

theorem selector_counts (hp : 7 < p)
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup)) :
    (∑ i : Fin 7, (w Variables.modeColumns[i]).val) = (w 0).val ∧
    (∑ i : Fin 5, (w Variables.iterationColumns[i]).val) = (w 0).val := by
  have bits := (control_bits h).2
  have counts := counts_field h
  constructor
  · apply count_value hp (sum := counts.1)
    intro i
    have flag := bits ⟨i.val, by omega⟩
    fin_cases i <;> exact flag
  · apply count_value (by omega) (sum := counts.2)
    intro i
    have flag := bits ⟨7 + i.val, by omega⟩
    fin_cases i <;> exact flag

theorem pointer_alignment (hp : 16777216 ≤ p)
    (inverse : 256 * (-7864320 : ZMod p) = 1)
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup)) :
    (w 13).val % 256 = 0 := by
  have bound := Verification.range16_bound
    (Verification.lookup_of_holds h ⟨0, by rw [lookup_count]; decide⟩)
  simp [Expression.eval, Verification.environment, limbBase] at bound
  have value := value_of_scaled_range hp (by decide) inverse
    (by simpa only [neg_mul] using bound)
  rw [value]
  simp

/-- Packed mode, iteration and round bits range the actual input control
    register. No external control-register bound or fixed-table rows are used. -/
theorem control_read_bound {p : Nat} [Fact p.Prime] (hp : 2048 ≤ p)
    {setup : Table (ZMod p) (fields 8)} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup)) :
    (w 3).val < 2048 := by
  have bits := (control_bits h).2
  have counts := selector_counts (by omega) h
  have exe := boolean_val (control_bits h).1
  let mode := ∑ i : Fin 7, i.val * (w Variables.modeColumns[i]).val
  let iteration := ∑ i : Fin 5, i.val * (w Variables.iterationColumns[i]).val
  let round := ∑ i : Fin 5, 2 ^ i.val * (w Variables.roundColumns[i]).val
  have modeBound : mode ≤ 6 := by
    calc
      mode ≤ ∑ i : Fin 7, 6 * (w Variables.modeColumns[i]).val :=
        Finset.sum_le_sum (fun i _ => Nat.mul_le_mul_right _ (by have := i.isLt; omega))
      _ = 6 * ∑ i : Fin 7, (w Variables.modeColumns[i]).val := (Finset.mul_sum _ _ _).symm
      _ ≤ 6 := by rw [counts.1]; omega
  have iterationBound : iteration ≤ 4 := by
    calc
      iteration ≤ ∑ i : Fin 5, 4 * (w Variables.iterationColumns[i]).val :=
        Finset.sum_le_sum (fun i _ => Nat.mul_le_mul_right _ (by have := i.isLt; omega))
      _ = 4 * ∑ i : Fin 5, (w Variables.iterationColumns[i]).val := (Finset.mul_sum _ _ _).symm
      _ ≤ 4 := by rw [counts.2]; omega
  have roundBit (i : Fin 5) : (w Variables.roundColumns[i]).val ≤ 1 := by
    have flag := boolean_val (bits ⟨12 + i.val, by omega⟩)
    fin_cases i <;> exact flag
  have roundBound : round ≤ 31 := by
    calc
      round ≤ ∑ i : Fin 5, 2 ^ i.val := by
        apply Finset.sum_le_sum
        intro i _
        simpa only [Nat.mul_one] using Nat.mul_le_mul_left (2 ^ i.val) (roundBit i)
      _ = 31 := by decide
  have packedBound : mode + 8 * iteration + 64 * round < p := by omega
  have definition := Verification.assertion_of_holds h ⟨3, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval, Verification.environment] at definition
  have field : ((mode + 8 * iteration + 64 * round : Nat) : ZMod p) = w 3 := by
    simp [mode, iteration, round, Variables.modeColumns, Variables.iterationColumns,
      Variables.roundColumns, Fin.sum_univ_succ]
    linear_combination definition
  have value : (w 3).val = mode + 8 * iteration + 64 * round := by
    rw [← field]
    exact ZMod.val_natCast_of_lt packedBound
  omega

theorem local_checks (hp : 16777216 ≤ p)
    (inverse : 256 * (-7864320 : ZMod p) = 1)
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup)) :
    LocalChecks w := by
  have bits := control_bits h
  have high := control_high_zero h
  have counts := selector_counts (by omega) h
  exact ⟨bits.1, bits.2, high.1, high.2, control_read_bound (by omega) h, counts.1, counts.2, pointer_alignment hp inverse h⟩

theorem round_bound {p : Nat} [Fact p.Prime]
    {setup : Table (ZMod p) (fields 8)} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup)) :
    (∑ i : Fin 5, 2 ^ i.val * (w Variables.roundColumns[i]).val) < 32 := by
  have bit (i : Fin 5) : (w Variables.roundColumns[i]).val ≤ 1 := by
    have bounded := boolean_val ((control_bits h).2 ⟨12 + i.val, by omega⟩)
    fin_cases i <;> exact bounded
  calc
    _ ≤ ∑ i : Fin 5, 2 ^ i.val := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [Nat.mul_one] using Nat.mul_le_mul_left (2 ^ i.val) (bit i)
    _ < 32 := by decide

end Airbender.Keccak.Proofs
