import Airbender.Proofs.Blake2Round.ExclusiveMask
import Airbender.Proofs.Arithmetic.OneHot
import Airbender.Proofs.BabyBear
import Airbender.Review.Trace.Workers.Blake2Round.Call
import Airbender.Proofs.Trace.Values

namespace Airbender.Blake2Round.Proofs
open Trace Arithmetic
open scoped BigOperators
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

theorem successful_mask {w : Nat → ZMod babyBearModulus}
    (core : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable)) (active : w 0 = 1) :
    ∃ round : Fin 10, Memory.RoundMask w round := by
  have bit (i : Fin 10) : (w Variables.roundBits[i]).val ≤ 1 := by
    have flag := Control.Proofs.control_bits core ⟨i.val + 3, by have := i.isLt; omega⟩
    fin_cases i <;> simpa [Variables.controlBits, Variables.roundBits, Fin.getElem_fin]
      using boolean_val flag
  have guard := Verification.assertion_of_holds core ⟨125, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment, active] at guard
  have field : (∑ i : Fin 10, w Variables.roundBits[i]) = 1 := by
    simp [Variables.roundBits, Fin.sum_univ_succ, Fin.getElem_fin]
    linear_combination guard
  have bound : (∑ i : Fin 10, (w Variables.roundBits[i]).val) < babyBearModulus := by
    have upper : (∑ i : Fin 10, (w Variables.roundBits[i]).val) ≤ 10 := by
      calc
        _ ≤ ∑ _ : Fin 10, (1 : Nat) := Finset.sum_le_sum (fun i _ => bit i)
        _ = 10 := by simp
    exact lt_of_le_of_lt upper (by decide)
  have total : (∑ i : Fin 10, (w Variables.roundBits[i]).val) = 1 := by
    apply bounded_nat_eq (F := ZMod babyBearModulus) (p := babyBearModulus) bound (by decide)
    simpa only [Nat.cast_sum, ZMod.natCast_zmod_val, Nat.cast_one] using field
  exact field_selection total

/-- Canonical controller flags and one native round are recovered from accepted
bits. No caller instruction/dataflow chain is needed. -/
theorem successful_position {w : Nat → ZMod babyBearModulus}
    (core : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable)) (active : w 0 = 1) :
    ∃ flags : Fin 8, ∃ index : Fin (if flags.val % 2 = 1 then 7 else 10),
      (readToken w importedConstraintsMemoryPorts[42]).word = controlAt flags index.val := by
  obtain ⟨round, mask⟩ := successful_mask core active
  obtain ⟨flags, packed⟩ := (exclusive_mask_iff (by decide) core round).mp mask
  have upper : round.val < if flags.val % 2 = 1 then 7 else 10 := by
    split_ifs with reduced
    · have mode := (control_flags (by decide) core flags round packed).1
      change (w 139).val = flags.val % 2 at mode
      have selected : w 139 = 1 := (ZMod.val_injective babyBearModulus)
        (by simpa only [ZMod.val_one, reduced] using mode)
      have guard := Verification.assertion_of_holds core ⟨126, by rw [constraint_count]; decide⟩
      simp [importedConstraints, FlatOperation.constraints, Expression.eval,
        Verification.environment, selected] at guard
      have m7 := mask 7; have m8 := mask 8; have m9 := mask 9
      fin_cases round <;> first
        | decide
        | (norm_num [Variables.roundBits] at m7 m8 m9; simp [m7, m8, m9] at guard)
    · exact round.isLt
  have canonical := Verification.assertion_of_holds core ⟨124, by rw [constraint_count]; decide⟩
  have low : w 135 = 0 := by
    simpa [importedConstraints, FlatOperation.constraints, Expression.eval,
      Verification.environment, active] using canonical
  have powerBound : 2 ^ round.val < 1024 := by fin_cases round <;> decide
  refine ⟨flags, ⟨round.val, upper⟩, ?_⟩
  simp [Trace.Proofs.read_word, importedConstraintsMemoryPorts, WordColumns.evaluate,
    controlAt, low, packed, Nat.mod_eq_of_lt powerBound]

end Airbender.Blake2Round.Proofs
