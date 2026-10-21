import Slop.Blake2Round.PreparationBase
import Slop.Blake2Round.PreparationExtended0
import Slop.Blake2Round.PreparationExtended1
import Slop.Blake2Round.PreparationExtended2
import Slop.Blake2Round.PreparationExtended3
import Slop.Blake2Round.ArtifactChecks
import Slop.Blake2Round.OpIndex
import Slop.Blake2G.OpIndex
import Human.Circuits.Blake2Round.Preparation
import Slop.Constraints
import Slop.Arithmetic.Lemmas
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases

namespace Airbender.Blake2Round.Preparation.Proofs
open Arithmetic

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

theorem chaining {p : Nat} [Fact p.Prime] (hp : 65536 ≤ p)
    {setup : Table (ZMod p) (fields 4)} {w : Nat → ZMod p} (compression : Bool)
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (selected : w 141 = if compression then 1 else 0) :
    words w Variables.chainingInputs =
      if compression then configuredIV else words w Variables.stateReads := by
  apply words_eq
  · intro i
    cases compression
    · exact read_bounds w Variables.stateReads i
    · fin_cases i <;> norm_num [configured_limbs] <;> omega
  intro i
  have lo := Verification.assertion_of_holds h ⟨4 + 4 * i.val,
    by rw [constraint_count]; have := i.isLt; omega⟩
  have high := Verification.assertion_of_holds h ⟨6 + 4 * i.val,
    by rw [constraint_count]; have := i.isLt; omega⟩
  cases compression <;> fin_cases i <;> op_index at lo high <;>
    simp [Expression.eval,
      Verification.environment, selected, words, Variables.chainingInputs,
      Variables.stateReads, configured_limbs] at lo high ⊢
  all_goals constructor
  all_goals first | linear_combination -lo | linear_combination -high

set_option maxHeartbeats 4000000 in
theorem extended {p : Nat} [Fact p.Prime] (hp : 65536 ≤ p)
    {setup : Table (ZMod p) (fields 4)} {w : Nat → ZMod p} (first compression : Bool)
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (firstFlag : w 142 = if first then 1 else 0)
    (compressionFlag : w 141 = if compression then 1 else 0) :
    words w Variables.preparedState = if first then words w Variables.chainingInputs ++
      (if compression then compressionIV
        else (iv.set 4 (words w Variables.extendedReads)[12]).set 6
          (words w Variables.extendedReads)[14])
      else words w Variables.extendedReads := by
  have normal := Verification.assertion_of_holds h ⟨3, by rw [constraint_count]; decide⟩
  op_index at normal
  simp [Expression.eval, Verification.environment] at normal
  have normalFlag : w 153 = (if first then 1 else 0) * (1 - if compression then 1 else 0) := by
    rw [← firstFlag, ← compressionFlag]
    linear_combination -normal
  apply words_eq
  · intro i
    cases first <;> cases compression
    all_goals simp only [Bool.false_eq_true, ↓reduceIte]
    all_goals simp only [Fin.getElem_fin, get_append8]
    all_goals fin_cases i <;> norm_num [words, Variables.chainingInputs, Variables.extendedReads,
      iv_limbs, compression_limbs]
    all_goals constructor
    all_goals first | exact ZMod.val_lt _ | omega
  intro i
  by_cases a : i.val < 4
  · exact extended_eqs_0 first compression h firstFlag compressionFlag normalFlag i (Nat.zero_le _) a
  by_cases b : i.val < 8
  · exact extended_eqs_1 first compression h firstFlag compressionFlag normalFlag i (by omega) b
  by_cases c : i.val < 12
  · exact extended_eqs_2 first compression h firstFlag compressionFlag normalFlag i (by omega) c
  exact extended_eqs_3 first compression h firstFlag compressionFlag normalFlag i (by omega)
    (by have := i.isLt; omega)

set_option maxHeartbeats 4000000 in
theorem message {p : Nat} [Fact p.Prime]
    {setup : Table (ZMod p) (fields 4)} {w : Nat → ZMod p} (compression right : Bool)
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (compressionFlag : w 141 = if compression then 1 else 0)
    (rightFlag : w 140 = if right then 1 else 0) :
    words w Variables.preparedMessage = if !compression then words w Variables.messageReads
      else if right then (words w Variables.messageReads).take 8 ++ words w Variables.stateReads
      else words w Variables.stateReads ++ (words w Variables.messageReads).take 8 := by
  have rightMode := Verification.assertion_of_holds h ⟨52, by rw [constraint_count]; decide⟩
  have leftMode := Verification.assertion_of_holds h ⟨53, by rw [constraint_count]; decide⟩
  op_index at rightMode leftMode
  simp [Expression.eval, Verification.environment] at rightMode leftMode
  have rightValue : w 202 = (if compression then 1 else 0) * (if right then 1 else 0) := by
    rw [← compressionFlag, ← rightFlag]
    linear_combination -rightMode
  have leftValue : w 203 = (if compression then 1 else 0) * (1 - if right then 1 else 0) := by
    rw [← compressionFlag, ← rightFlag]
    linear_combination -leftMode
  apply words_eq
  · intro i
    cases compression <;> cases right
    all_goals simp only [Bool.false_eq_true, Bool.not_false, Bool.not_true, ↓reduceIte]
    all_goals simp only [Fin.getElem_fin, get_path_left, get_path_right]
    all_goals fin_cases i <;> norm_num [words, Variables.messageReads, Variables.stateReads]
    all_goals exact ⟨ZMod.val_lt _, ZMod.val_lt _⟩
  intro i
  have lo := Verification.assertion_of_holds h ⟨54 + 2 * i.val,
    by rw [constraint_count]; have := i.isLt; omega⟩
  have high := Verification.assertion_of_holds h ⟨55 + 2 * i.val,
    by rw [constraint_count]; have := i.isLt; omega⟩
  clear h rightMode leftMode
  fin_cases i <;> op_index at lo high <;> simp [Expression.eval,
    Verification.environment] at lo high
  all_goals cases compression <;> cases right
  all_goals simp only [Bool.false_eq_true, Bool.not_false, Bool.not_true, ↓reduceIte]
  all_goals simp only [Fin.getElem_fin, get_path_left, get_path_right]
  all_goals simp [compressionFlag, rightValue, leftValue, words,
    Variables.preparedMessage, Variables.messageReads, Variables.stateReads] at lo high ⊢
  all_goals constructor
  all_goals first | linear_combination -lo | linear_combination -high

theorem soundness {p : Nat} [Fact p.Prime] (hp : 65536 ≤ p)
    (setup : Table (ZMod p) (fields 4)) :
    Properties.Soundness (circuitModel setup).relation spec := by
  intro input output w ⟨h, mapping⟩
  have chain := chaining hp input.compression h mapping.compression
  have state := extended hp input.firstRound input.compression h mapping.firstRound mapping.compression
  have msg := message input.compression input.inputIsRight h mapping.compression mapping.inputIsRight
  obtain ⟨_, _, _, stateInput, extendedInput, messageInput, chainOutput, extendedOutput, messageOutput⟩ := mapping
  unfold spec step
  cases output
  simp only at chainOutput extendedOutput messageOutput
  rw [chainOutput, extendedOutput, messageOutput, stateInput, extendedInput, messageInput]
  rw [state, msg, chain]

end Airbender.Blake2Round.Preparation.Proofs
