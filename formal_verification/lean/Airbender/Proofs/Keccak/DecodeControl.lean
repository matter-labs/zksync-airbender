import Airbender.Proofs.Keccak.Tags
import Airbender.Review.Keccak.ControlUpdate

namespace Airbender.Keccak.Proofs
open Arithmetic
open scoped BigOperators
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000

theorem decoded_control {p : Nat} [Fact p.Prime] (hp : 2048 ≤ p)
    {setup : Table (ZMod p) (fields 8)} {w : Nat → ZMod p} (s : ControlState)
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (active : w 0 = 1) (input : (w 3).val = s.packed) :
    (∀ i : Fin 7, w Variables.modeColumns[i] = if i = s.mode then 1 else 0) ∧
    (∀ i : Fin 5, w Variables.iterationColumns[i] = if i = s.iteration then 1 else 0) ∧
    w 75 + 2 * w 76 + 4 * w 77 + 8 * w 78 + 16 * w 79 = (s.round.val : ZMod p) := by
  have counts := selector_counts (by omega) h
  have one : (1 : ZMod p).val = 1 := by
    simpa only [Nat.cast_one] using ZMod.val_natCast_of_lt (n := p) (a := 1) (by omega)
  rw [active, one] at counts
  obtain ⟨mode, modes⟩ := field_selection counts.1
  obtain ⟨iteration, iterations⟩ := field_selection counts.2
  let round := ∑ i : Fin 5, 2 ^ i.val * (w Variables.roundColumns[i]).val
  have rb : round < 32 := round_bound h
  have rf : (round : ZMod p) = w 75 + 2 * w 76 + 4 * w 77 + 8 * w 78 + 16 * w 79 := by
    simp [round, Variables.roundColumns, Fin.sum_univ_succ]
    ring
  have m0 := modes 0; have m1 := modes 1; have m2 := modes 2
  have m3 := modes 3; have m4 := modes 4; have m5 := modes 5; have m6 := modes 6
  have i0 := iterations 0; have i1 := iterations 1; have i2 := iterations 2
  have i3 := iterations 3; have i4 := iterations 4
  have equation := Verification.assertion_of_holds h ⟨3, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment] at equation
  have field : w 3 = ((mode.val + 8 * iteration.val + 64 * round : Nat) : ZMod p) := by
    fin_cases mode <;> fin_cases iteration
    all_goals simp [Variables.modeColumns] at m0 m1 m2 m3 m4 m5 m6
    all_goals simp [Variables.iterationColumns] at i0 i1 i2 i3 i4
    all_goals simp [m1, m2, m3, m4, m5, m6, i1, i2, i3, i4] at equation
    all_goals simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, rf]
    all_goals linear_combination -equation
  have bound : mode.val + 8 * iteration.val + 64 * round < p := by
    have := mode.isLt; have := iteration.isLt
    omega
  have value := congrArg ZMod.val field
  rw [ZMod.val_natCast_of_lt bound, input] at value
  have same : mode = s.mode ∧ iteration = s.iteration ∧ round = s.round.val := by
    have := mode.isLt; have := iteration.isLt
    have := s.mode.isLt; have := s.iteration.isLt; have := s.round.isLt
    simp only [ControlState.packed] at value
    have r : round = s.round.val := by omega
    have i : iteration.val = s.iteration.val := by omega
    have m : mode.val = s.mode.val := by omega
    exact ⟨Fin.ext m, Fin.ext i, r⟩
  exact ⟨by simpa only [same.1] using modes,
    by simpa only [same.2.1] using iterations, by rw [← rf, same.2.2]⟩

end Airbender.Keccak.Proofs
