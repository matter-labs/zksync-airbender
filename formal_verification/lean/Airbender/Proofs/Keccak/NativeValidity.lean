import Airbender.Proofs.Keccak.DecodeControl
import Airbender.Proofs.BabyBear
import Airbender.Review.Trace.Workers.Keccak.Call
import Airbender.Proofs.Trace.Values
import Airbender.Review.Circuits.Keccak.Tables.Controller

namespace Airbender.Keccak.Proofs
open Trace Arithmetic
open scoped BigOperators
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

private abbrev SuccessfulControl (s : ControlState) : Prop :=
  s.round.val ≤ 24 ∧ (s.round.val = 24 → s.mode.val = 0 ∧ s.iteration.val = 0) ∧
    (s.mode.val = 1 ∨ s.mode.val = 2 → s.iteration.val = 0)

private def indexOf (s : ControlState) : Nat :=
  27 * s.round.val + if s.mode.val = 0 then s.iteration.val
    else if s.mode.val = 1 then 5 else if s.mode.val = 2 then 6
    else if s.mode.val = 3 then 7 + s.iteration.val
    else if s.mode.val = 4 then 12 + s.iteration.val
    else if s.mode.val = 5 then 17 + 2 * s.iteration.val else 18 + 2 * s.iteration.val

private theorem control_certificate : ∀ mode : Fin 7, ∀ iteration : Fin 5, ∀ round : Fin 32,
    let bit := fun i : Nat => ((round.val / 2 ^ i % 2 : Nat) : ZMod babyBearModulus)
    let high := bit 3 * bit 4
    let low := bit 0 + 2 * bit 1 + 4 * bit 2
    let m0 : ZMod babyBearModulus := if (0 : Fin 7) = mode then 1 else 0
    let m1 : ZMod babyBearModulus := if (1 : Fin 7) = mode then 1 else 0
    let m2 : ZMod babyBearModulus := if (2 : Fin 7) = mode then 1 else 0
    let i0 : ZMod babyBearModulus := if (0 : Fin 5) = iteration then 1 else 0
    high * (low + 1 - m0) = 0 ∧ m1 * (1 - i0) = 0 ∧
      m2 * (1 - i0) = 0 ∧ high * (1 - i0) = 0 →
    SuccessfulControl ⟨mode, iteration, round⟩ := by
  decide +kernel

private theorem index_certificate : ∀ mode : Fin 7, ∀ iteration : Fin 5, ∀ round : Fin 32,
    let s : ControlState := ⟨mode, iteration, round⟩
    SuccessfulControl s → indexOf s < 649 ∧
      (scheduleControl ⟨indexOf s % 650, Nat.mod_lt _ (by decide)⟩).packed = s.packed := by
  decide +kernel

private theorem native_round_bits {w : Nat → ZMod babyBearModulus} (s : ControlState)
    (core : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints (setupTable Controller.rows)))
    (active : w 0 = 1) (read : (w 3).val = s.packed) :
    ∀ i : Fin 5, w Variables.roundColumns[i] = ((s.round.val / 2 ^ i.val % 2 : Nat) : ZMod babyBearModulus) := by
  have bits (i : Fin 5) : (w Variables.roundColumns[i]).val ≤ 1 := by
    have flag := (control_bits core).2 ⟨12 + i.val, by have := i.isLt; omega⟩
    fin_cases i <;> simpa [Variables.roundColumns, Fin.getElem_fin] using boolean_val flag
  have decoded := (decoded_control (by decide) s core active read).2.2
  have field : ((∑ i : Fin 5, 2 ^ i.val * (w Variables.roundColumns[i]).val : Nat) :
      ZMod babyBearModulus) = (s.round.val : ZMod babyBearModulus) := by
    simpa [Variables.roundColumns, Fin.sum_univ_succ, Fin.getElem_fin, add_assoc] using decoded
  have natural : (∑ i : Fin 5, 2 ^ i.val * (w Variables.roundColumns[i]).val) = s.round.val := by
    apply bounded_nat_eq (F := ZMod babyBearModulus) (p := babyBearModulus) ?_ ?_ field
    · exact lt_trans (round_bound core) (by decide)
    · exact lt_trans s.round.isLt (by decide)
  have b0 := bits 0; have b1 := bits 1; have b2 := bits 2
  have b3 := bits 3; have b4 := bits 4
  simp [Variables.roundColumns, Fin.sum_univ_succ, Fin.getElem_fin] at natural
  simp [Variables.roundColumns, Fin.getElem_fin] at b0 b1 b2 b3 b4
  intro i
  apply ZMod.val_injective babyBearModulus
  have canonical : s.round.val / 2 ^ i.val % 2 < babyBearModulus :=
    lt_trans (Nat.mod_lt _ (by decide)) (by decide)
  rw [ZMod.val_natCast_of_lt canonical]
  fin_cases i
  all_goals norm_num [Variables.roundColumns, Fin.getElem_fin] at natural ⊢
  all_goals omega

/-- Native mode/iteration/round constraints select one of the pinned successful
Keccak positions, independently of any instruction occurrence plan. -/
theorem successful_position {w : Nat → ZMod babyBearModulus}
    (core : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints (setupTable Controller.rows))) (active : w 0 = 1) :
    ∃ index : Fin 649,
      (readToken w importedConstraintsMemoryPorts[0]).word =
        ⟨(scheduleControl ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩).packed, 0⟩ := by
  obtain ⟨s, read, _⟩ := (control_update_checks (by decide) core).active active
  have decoded := decoded_control (by decide) s core active read
  have m0 := decoded.1 0; have m1 := decoded.1 1; have m2 := decoded.1 2
  have i0 := decoded.2.1 0
  simp [Variables.modeColumns, Fin.getElem_fin] at m0 m1 m2
  simp [Variables.iterationColumns, Fin.getElem_fin] at i0
  have b0 := native_round_bits s core active read 0
  have b1 := native_round_bits s core active read 1
  have b2 := native_round_bits s core active read 2
  have b3 := native_round_bits s core active read 3
  have b4 := native_round_bits s core active read 4
  simp [Variables.roundColumns, Fin.getElem_fin] at b0 b1 b2 b3 b4
  have definition := Verification.assertion_of_holds core ⟨156, by rw [constraint_count]; decide⟩
  have guard := Verification.assertion_of_holds core ⟨157, by rw [constraint_count]; decide⟩
  have mix1 := Verification.assertion_of_holds core ⟨158, by rw [constraint_count]; decide⟩
  have mix2 := Verification.assertion_of_holds core ⟨159, by rw [constraint_count]; decide⟩
  have final := Verification.assertion_of_holds core ⟨160, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment, -mul_eq_zero] at definition guard mix1 mix2 final
  have high : w 222 = w 78 * w 79 := by linear_combination -definition
  have valid : SuccessfulControl s := by
    apply control_certificate s.mode s.iteration s.round
    dsimp only
    norm_num only [Nat.reducePow, Nat.div_one]
    simp only [high, b0, b1, b2, b3, b4, m0, m1, m2, i0] at guard mix1 mix2 final
    exact ⟨by convert guard using 1; ring,
      by convert mix1 using 1; ring, by convert mix2 using 1; ring,
      by convert final using 1; ring⟩
  obtain ⟨bound, packed⟩ := index_certificate s.mode s.iteration s.round valid
  refine ⟨⟨indexOf s, bound⟩, ?_⟩
  have highZero := (control_high_zero core).1
  have raw : (readToken w importedConstraintsMemoryPorts[0]).word = ⟨s.packed, 0⟩ := by
    simp [Trace.Proofs.read_word, importedConstraintsMemoryPorts, WordColumns.evaluate, read, highZero]
  apply raw.trans
  apply congrArg (fun value => (⟨value, 0⟩ : Word))
  have bound650 : indexOf s < 650 := Nat.lt_trans bound (by decide : 649 < 650)
  simpa only [Nat.mod_eq_of_lt bound650] using packed.symm

end Airbender.Keccak.Proofs
