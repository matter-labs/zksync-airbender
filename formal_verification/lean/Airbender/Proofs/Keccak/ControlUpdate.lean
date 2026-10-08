import Airbender.Review.Keccak.ControlUpdate
import Airbender.Proofs.Keccak.Controls
import Airbender.Proofs.Arithmetic.OneHot

namespace Airbender.Keccak.Proofs
open Arithmetic
open scoped BigOperators
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000

private theorem round_bound {p : Nat} [Fact p.Prime]
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

private theorem selected_update {p : Nat} [Fact p.Prime] (hp : 4096 ≤ p)
    {setup : Table (ZMod p) (fields 8)} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (mode : Fin 7) (iteration : Fin 5)
    (modes : ∀ i : Fin 7, w Variables.modeColumns[i] = if i = mode then 1 else 0)
    (iterations : ∀ i : Fin 5, w Variables.iterationColumns[i] = if i = iteration then 1 else 0) :
    ∃ s : ControlState, (w 3).val = s.packed ∧ (w 5).val = s.nextPacked := by
  let round := ∑ i : Fin 5, 2 ^ i.val * (w Variables.roundColumns[i]).val
  have roundBound : round < 32 := round_bound h
  let s : ControlState := ⟨mode, iteration, ⟨round, roundBound⟩⟩
  have roundField : (round : ZMod p) = w 75 + 2 * w 76 + 4 * w 77 + 8 * w 78 + 16 * w 79 := by
    simp [round, Variables.roundColumns, Fin.sum_univ_succ]
    ring
  have m0 := modes 0; have m1 := modes 1; have m2 := modes 2
  have m3 := modes 3; have m4 := modes 4; have m5 := modes 5; have m6 := modes 6
  have i0 := iterations 0; have i1 := iterations 1; have i2 := iterations 2
  have i3 := iterations 3; have i4 := iterations 4
  have input := Verification.assertion_of_holds h ⟨3, by rw [constraint_count]; decide⟩
  have output := Verification.assertion_of_holds h ⟨8, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval, Verification.environment] at input output
  have fields : w 3 = (s.packed : ZMod p) ∧ w 5 = (s.nextPacked : ZMod p) := by
    fin_cases mode <;> fin_cases iteration
    all_goals simp [Variables.modeColumns] at m0 m1 m2 m3 m4 m5 m6
    all_goals simp [Variables.iterationColumns] at i0 i1 i2 i3 i4
    all_goals simp [m1, m2, m3, m4, m5, m6, i1, i2, i3, i4] at input
    all_goals simp [m0, m1, m2, m3, m4, m5, m6, i1, i2, i3, i4] at output
    all_goals simp [s, ControlState.packed, ControlState.nextPacked, roundField]
    all_goals constructor
    all_goals first | linear_combination -input | linear_combination -output
  have inputBound : s.packed < p := by
    dsimp [s, ControlState.packed]
    have := mode.isLt; have := iteration.isLt
    omega
  have outputBound : s.nextPacked < p := by
    fin_cases mode <;> fin_cases iteration <;>
      simp [s, ControlState.nextPacked] <;> omega
  refine ⟨s, ?_, ?_⟩
  · rw [fields.1, ZMod.val_natCast_of_lt inputBound]
  · rw [fields.2, ZMod.val_natCast_of_lt outputBound]

/-- The local controller progression is a consequence of imported equations,
    for any fixed setup, independently of the controller table's supplied rows. -/
theorem control_update_checks {p : Nat} [Fact p.Prime] (hp : 4096 ≤ p)
    {setup : Table (ZMod p) (fields 8)} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup)) :
    ControlUpdateChecks w := by
  have counts := selector_counts (by omega) h
  constructor
  · intro inactive
    rw [inactive, ZMod.val_zero] at counts
    have modeZero (i : Fin 7) : w Variables.modeColumns[i] = 0 := by
      have bound := Finset.single_le_sum (f := fun i : Fin 7 => (w Variables.modeColumns[i]).val)
        (fun i _ => Nat.zero_le _) (Finset.mem_univ i)
      have zero : (w Variables.modeColumns[i]).val = 0 := by omega
      have cast := ZMod.natCast_zmod_val (w Variables.modeColumns[i])
      simpa only [zero, Nat.cast_zero] using cast.symm
    have m0 := modeZero 0; have m1 := modeZero 1; have m2 := modeZero 2
    have m3 := modeZero 3; have m4 := modeZero 4; have m5 := modeZero 5; have m6 := modeZero 6
    simp [Variables.modeColumns] at m0 m1 m2 m3 m4 m5 m6
    have input := Verification.assertion_of_holds h ⟨3, by rw [constraint_count]; decide⟩
    have output := Verification.assertion_of_holds h ⟨8, by rw [constraint_count]; decide⟩
    simp [importedConstraints, FlatOperation.constraints, Expression.eval, Verification.environment,
      m0, m1, m2, m3, m4, m5, m6] at input output
    linear_combination input - output
  · intro active
    rw [active] at counts
    have one : (1 : ZMod p).val = 1 := by
      simpa only [Nat.cast_one] using ZMod.val_natCast_of_lt (n := p) (a := 1) (by omega)
    rw [one] at counts
    obtain ⟨mode, modes⟩ := field_selection counts.1
    obtain ⟨iteration, iterations⟩ := field_selection counts.2
    exact selected_update hp h mode iteration modes iterations

end Airbender.Keccak.Proofs
