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

private theorem iv_limbs : iv = #v[
    ⟨58983, 27145⟩, ⟨44677, 47975⟩, ⟨62322, 15470⟩, ⟨62778, 42319⟩,
    ⟨21119, 20750⟩, ⟨26764, 39685⟩, ⟨55723, 8067⟩, ⟨52505, 23520⟩] := by
  apply Vector.ext
  intro i hi
  interval_cases i <;> norm_num [iv, configuredIV, compressionIV, Specs.BLAKE3.iv, splitWord, limbBase]
  all_goals decide

private theorem configured_limbs : configuredIV = #v[
    ⟨58951, 27400⟩, ⟨44677, 47975⟩, ⟨62322, 15470⟩, ⟨62778, 42319⟩,
    ⟨21119, 20750⟩, ⟨26764, 39685⟩, ⟨55723, 8067⟩, ⟨52505, 23520⟩] := by
  apply Vector.ext
  intro i hi
  interval_cases i <;> norm_num [iv, configuredIV, compressionIV, Specs.BLAKE3.iv, splitWord, limbBase]
  all_goals decide

private theorem compression_limbs : compressionIV = #v[
    ⟨58983, 27145⟩, ⟨44677, 47975⟩, ⟨62322, 15470⟩, ⟨62778, 42319⟩,
    ⟨21055, 20750⟩, ⟨26764, 39685⟩, ⟨9812, 57468⟩, ⟨52505, 23520⟩] := by
  apply Vector.ext
  intro i hi
  interval_cases i <;> norm_num [iv, configuredIV, compressionIV, Specs.BLAKE3.iv, splitWord, limbBase]
  all_goals decide

private theorem get_append8 (xs ys : Vector Word 8) (i : Nat) (hi : i < 16) :
    (show Vector Word 16 from xs ++ ys)[i] = if h : i < 8 then xs[i] else ys[i - 8] := by
  exact Vector.getElem_append (xs := xs) (ys := ys) hi
private theorem get_path_left (xs : Vector Word 16) (ys : Vector Word 8) (i : Nat) (hi : i < 16) :
    (show Vector Word 16 from xs.take 8 ++ ys)[i] = if h : i < 8 then xs[i] else ys[i - 8] := by
  have e : (show Vector Word 16 from xs.take 8 ++ ys)[i] =
      if h : i < 8 then (xs.take 8)[i] else ys[i - 8] :=
    Vector.getElem_append (xs := xs.take 8) (ys := ys) hi
  rw [e]
  split
  · exact Vector.getElem_take (xs := xs) (j := 8) (by omega)
  · rfl
private theorem get_path_right (xs : Vector Word 8) (ys : Vector Word 16) (i : Nat) (hi : i < 16) :
    (show Vector Word 16 from xs ++ ys.take 8)[i] = if h : i < 8 then xs[i] else ys[i - 8] := by
  have e : (show Vector Word 16 from xs ++ ys.take 8)[i] =
      if h : i < 8 then xs[i] else (ys.take 8)[i - 8] :=
    Vector.getElem_append (xs := xs) (ys := ys.take 8) hi
  rw [e]
  split
  · rfl
  · exact Vector.getElem_take (xs := ys) (j := 8) (by omega)

private theorem words_eq {p n : Nat} [Fact p.Prime] {w : Nat → ZMod p}
    {columns : Vector (Nat × Nat) n} {expected : Vector Word n}
    (bounds : ∀ i : Fin n, expected[i].lo < p ∧ expected[i].hi < p)
    (equalities : ∀ i : Fin n, w columns[i].1 = (expected[i].lo : ZMod p) ∧
      w columns[i].2 = (expected[i].hi : ZMod p)) : words w columns = expected := by
  apply Vector.ext
  intro i hi
  obtain ⟨lo, high⟩ := equalities ⟨i, hi⟩
  obtain ⟨loBound, hiBound⟩ := bounds ⟨i, hi⟩
  simp only [Fin.getElem_fin] at lo high loBound hiBound
  simp only [words, Vector.getElem_map]
  rw [lo, high, ZMod.val_natCast_of_lt loBound, ZMod.val_natCast_of_lt hiBound]

private theorem read_bounds {p n : Nat} [Fact p.Prime] (w : Nat → ZMod p)
    (columns : Vector (Nat × Nat) n) (i : Fin n) :
    (words w columns)[i].lo < p ∧ (words w columns)[i].hi < p := by
  simp only [words, Fin.getElem_fin, Vector.getElem_map]
  exact ⟨ZMod.val_lt _, ZMod.val_lt _⟩

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
  let loIndices : Vector Nat 16 := #v[5, 9, 13, 17, 21, 25, 29, 33, 36, 38, 40, 42, 48, 44, 50, 46]
  let hiIndices : Vector Nat 16 := #v[7, 11, 15, 19, 23, 27, 31, 35, 37, 39, 41, 43, 49, 45, 51, 47]
  have lo := Verification.assertion_of_holds h ⟨loIndices[i],
    by rw [constraint_count]; fin_cases i <;> norm_num [loIndices]⟩
  have high := Verification.assertion_of_holds h ⟨hiIndices[i],
    by rw [constraint_count]; fin_cases i <;> norm_num [hiIndices]⟩
  clear h normal
  fin_cases i <;> simp only [loIndices, hiIndices, Fin.getElem_fin, Vector.getElem_mk,
    List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ] at lo high <;>
    op_index at lo high <;> simp [Expression.eval, Verification.environment] at lo high
  all_goals cases first <;> cases compression
  all_goals simp only [Bool.false_eq_true, ↓reduceIte]
  all_goals simp only [Fin.getElem_fin, get_append8]
  all_goals simp [firstFlag, compressionFlag, normalFlag, words, Variables.preparedState,
    Variables.chainingInputs, Variables.extendedReads, iv_limbs, compression_limbs] at lo high ⊢
  all_goals constructor
  all_goals first | linear_combination -lo | linear_combination -high

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
