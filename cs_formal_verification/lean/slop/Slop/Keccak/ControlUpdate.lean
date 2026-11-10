module
public import Human.Circuits.Keccak.ControlUpdate
public import Slop.Keccak.Controls
public import Slop.Keccak.OpIndex
public import Slop.Arithmetic.OneHot
public import Slop.CleanCore.Circuit.Operations
public import Slop.Defs.Circuits.Keccak.Artifact

@[expose] public section

namespace Airbender.Keccak.Proofs
open Arithmetic
open scoped BigOperators
set_option warningAsError true

/-- The position of the selected mode, as the sum of the one-hot flags it weighs. -/
private theorem mode_sum : ∀ mode : Fin 7, (mode.val : Nat) =
    (if (1 : Fin 7) = mode then 1 else 0) + 2 * (if (2 : Fin 7) = mode then 1 else 0) +
    3 * (if (3 : Fin 7) = mode then 1 else 0) + 4 * (if (4 : Fin 7) = mode then 1 else 0) +
    5 * (if (5 : Fin 7) = mode then 1 else 0) + 6 * (if (6 : Fin 7) = mode then 1 else 0) := by
  decide

private theorem iteration_sum : ∀ iteration : Fin 5, (iteration.val : Nat) =
    (if (1 : Fin 5) = iteration then 1 else 0) + 2 * (if (2 : Fin 5) = iteration then 1 else 0) +
    3 * (if (3 : Fin 5) = iteration then 1 else 0) + 4 * (if (4 : Fin 5) = iteration then 1 else 0) := by
  decide

/-- The next control word without the round. -/
private def nextBase (mode : Fin 7) (iteration : Fin 5) : Nat := (ControlState.mk mode iteration 0).nextPacked

private theorem next_round (s : ControlState) :
    s.nextPacked = nextBase s.mode s.iteration + 64 * s.round.val := by
  unfold nextBase ControlState.nextPacked
  dsimp only
  split_ifs <;> omega

private theorem next_bound (s : ControlState) : s.nextPacked < 4096 := by
  have := s.round.isLt; have := s.mode.isLt; have := s.iteration.isLt
  unfold ControlState.nextPacked
  dsimp only
  split_ifs <;> omega

/-- The next control word as the imported output equation weighs the one-hot flags (its negative
    terms moved to the left). -/
private theorem next_base_flags : ∀ (mode : Fin 7) (iteration : Fin 5),
    nextBase mode iteration + (if (6 : Fin 7) = mode then 1 else 0) *
        (1 + 5 * (if (4 : Fin 5) = iteration then 1 else 0)) +
      40 * ((if (0 : Fin 7) = mode then 1 else 0) + (if (3 : Fin 7) = mode then 1 else 0) +
        (if (4 : Fin 7) = mode then 1 else 0) + (if (6 : Fin 7) = mode then 1 else 0)) *
        (if (4 : Fin 5) = iteration then 1 else 0) =
    mode.val + ((if (1 : Fin 7) = mode then 1 else 0) + (if (2 : Fin 7) = mode then 1 else 0) +
        (if (5 : Fin 7) = mode then 1 else 0)) +
      ((if (0 : Fin 7) = mode then 1 else 0) + (if (3 : Fin 7) = mode then 1 else 0) +
        (if (4 : Fin 7) = mode then 1 else 0)) * (if (4 : Fin 5) = iteration then 1 else 0) +
      8 * iteration.val +
      8 * ((if (0 : Fin 7) = mode then 1 else 0) + (if (3 : Fin 7) = mode then 1 else 0) +
        (if (4 : Fin 7) = mode then 1 else 0) + (if (6 : Fin 7) = mode then 1 else 0)) +
      64 * (if (6 : Fin 7) = mode then 1 else 0) * (if (4 : Fin 5) = iteration then 1 else 0) := by
  decide

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
  have input := Verification.assertion_of_holds h ⟨3, by rw [constraint_count]; decide⟩
  have output := Verification.assertion_of_holds h ⟨8, by rw [constraint_count]; decide⟩
  op_index at input output
  simp only [Expression.eval, Verification.environment, Int.ofNat_eq_natCast, Nat.cast_ofNat, Nat.cast_one,
    Nat.cast_zero, Int.cast_negSucc, Int.cast_one, Int.cast_ofNat, Int.cast_zero,
    show w 63 = _ from modes 0, show w 64 = _ from modes 1, show w 65 = _ from modes 2,
    show w 66 = _ from modes 3, show w 67 = _ from modes 4, show w 68 = _ from modes 5,
    show w 69 = _ from modes 6, show w 71 = _ from iterations 1, show w 72 = _ from iterations 2,
    show w 73 = _ from iterations 3, show w 74 = _ from iterations 4] at input output
  have hm := congrArg (Nat.cast : Nat → ZMod p) (mode_sum mode)
  have hi := congrArg (Nat.cast : Nat → ZMod p) (iteration_sum iteration)
  have hn := congrArg (Nat.cast : Nat → ZMod p) (next_base_flags mode iteration)
  push_cast at hm hi hn
  have fields : w 3 = (s.packed : ZMod p) ∧ w 5 = (s.nextPacked : ZMod p) := by
    constructor
    · simp only [s, ControlState.packed]
      push_cast
      linear_combination -input - hm - 8 * hi - 64 * roundField
    · rw [next_round]
      push_cast
      linear_combination -output - hm - 8 * hi - hn - 64 * roundField
  have inputBound : s.packed < p := by
    dsimp [s, ControlState.packed]
    have := mode.isLt; have := iteration.isLt
    omega
  have outputBound : s.nextPacked < p := lt_of_lt_of_le (next_bound s) hp
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
    op_index at input output
    simp [Expression.eval, Verification.environment, m0, m1, m2, m3, m4, m5, m6] at input output
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
