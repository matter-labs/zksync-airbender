import Slop.Blake2Round.FinalXor
import Slop.Blake2Round.OpIndex

set_option warningAsError true
-- one call's goals may not use every lemma of the shared simp set
set_option linter.unusedSimpArgs false

namespace Airbender.Blake2Round.Proofs

open Arithmetic Blake2G.Proofs

set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

/-- The selected final-output mux (constraints 108..123) exposes the actual
    seven/nine- or eight/eight-bit assembly of the last two queries of each limb.
    All sixteen state-write equations are checked. -/
theorem final_write {p : Nat} [Fact p.Prime] (limb : Fin 16) {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable)) (enabled : w 152 = 1) :
    w (7 + 4 * (limb.val / 2) + limb.val % 2) =
      finalColumn w limb 2 2 + (if limb.val < 8 then 128 else 256) * finalColumn w limb 3 2 := by
  have equation := Verification.assertion_of_holds h
    ⟨108 + limb.val, by rw [constraint_count]; have := limb.isLt; omega⟩
  clear h
  fin_cases limb
  all_goals simp only [finalColumn, finalQuery, Fin.isValue, Fin.val_zero, Fin.val_one,
    Fin.val_two, Fin.val_mk, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceMul, Nat.reduceAdd,
    Nat.reduceDiv] at equation ⊢
  all_goals op_index at equation ⊢
  all_goals simp [Expression.eval, Verification.environment, enabled] at equation ⊢
  all_goals linear_combination -equation

private theorem tag_cast {p : Nat} [Fact p.Prime] {x : ZMod p} {t : Nat} (kind : Fin 3)
    (value : x = (t : ZMod p)) (index : #v[4, 19, 20][kind] = t) :
    x = ((#v[4, 19, 20][kind] : Nat) : ZMod p) := by
  rw [index]; exact value

/-- The a/c half of finalization needs no external limb bounds: the four
    imported queries bound and identify each of its three XOR inputs. -/
theorem ac_limb_xor {p : Nat} [Fact p.Prime] (hp : 65536 ≤ p)
    (compatible : 64 * (-31457280 : ZMod p) = 1) (limb : Fin 8)
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable)) (enabled : w 152 = 1) :
    (acInitial w limb).val < 65536 ∧ (acA w limb).val < 65536 ∧
    (acC w limb).val < 65536 ∧
    (w (7 + 4 * (limb.val / 2) + limb.val % 2)).val < 65536 ∧
    (w (7 + 4 * (limb.val / 2) + limb.val % 2)).val =
      (acInitial w limb).val ^^^ (acA w limb).val ^^^ (acC w limb).val := by
  have field : p = 2013265921 := serialized_field compatible
  obtain ⟨t0, t1, t2, t3, initial, c, link0, link1, a⟩ := ac_shape field limb w
  have q0 := final_query (by omega) (limb.castLE (by omega)) 0 1 h
    (tag_cast 1 (by exact_mod_cast t0) rfl)
  have q1 := final_query (by omega) (limb.castLE (by omega)) 1 2 h
    (tag_cast 2 (by exact_mod_cast t1) rfl)
  have q2 := final_query (by omega) (limb.castLE (by omega)) 2 1 h
    (tag_cast 1 (by exact_mod_cast t2) rfl)
  have q3 := final_query (by omega) (limb.castLE (by omega)) 3 2 h
    (tag_cast 2 (by exact_mod_cast t3) rfl)
  have r : ((2 ^ 7 : Nat) : ZMod p) = 128 := by norm_num
  have first := xor_limb_chunks hp (width := 7) (remaining := 9) (by decide) q0 q1
    (x := acInitial w limb) (y := acC w limb)
    (z := finalColumn w (limb.castLE (by omega)) 0 2 +
      ((2 ^ 7 : Nat) : ZMod p) * finalColumn w (limb.castLE (by omega)) 1 2)
    (by rw [r]; exact initial) (by rw [r]; exact c) rfl
  have write := final_write (limb.castLE (by omega)) h enabled
  have activeWrite : w (7 + 4 * (limb.val / 2) + limb.val % 2) =
      finalColumn w (limb.castLE (by omega)) 2 2 +
        ((2 ^ 7 : Nat) : ZMod p) * finalColumn w (limb.castLE (by omega)) 3 2 := by
    rw [r]
    simpa only [Fin.val_castLE, ite_eq_left limb.isLt] using write
  have second := xor_limb_chunks hp (width := 7) (remaining := 9) (by decide) q2 q3
    (y := acA w limb) (by rw [link0, link1]) (by rw [r]; exact a) activeWrite
  refine ⟨first.1, second.2.1, first.2.1, second.2.2.1, ?_⟩
  rw [second.2.2.2, first.2.2.2]
  ac_rfl

/-- The b/d half changes chunk width between its two XORs. The imported query
    expressions, not the witness generator, supply that change of decomposition. -/
theorem bd_limb_xor {p : Nat} [Fact p.Prime] (hp : 65536 ≤ p)
    (compatible : 64 * (-31457280 : ZMod p) = 1) (limb : Fin 8)
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable)) (enabled : w 152 = 1) :
    (bdInitial w limb).val < 65536 ∧ (bdB w limb).val < 65536 ∧
    (bdD w limb).val < 65536 ∧
    (w (23 + 4 * (limb.val / 2) + limb.val % 2)).val < 65536 ∧
    (w (23 + 4 * (limb.val / 2) + limb.val % 2)).val =
      (bdInitial w limb).val ^^^ (bdB w limb).val ^^^ (bdD w limb).val := by
  have field : p = 2013265921 := serialized_field compatible
  obtain ⟨t0, t1, t2, t3, b, initial, regroup, d⟩ := bd_shape field limb w
  let index : Fin 16 := ⟨8 + limb.val, by omega⟩
  have q0 := final_query (by omega) index 0 2 h (tag_cast 2 (by exact_mod_cast t0) rfl)
  have q1 := final_query (by omega) index 1 1 h (tag_cast 1 (by exact_mod_cast t1) rfl)
  have q2 := final_query (by omega) index 2 0 h (tag_cast 0 (by exact_mod_cast t2) rfl)
  have q3 := final_query (by omega) index 3 0 h (tag_cast 0 (by exact_mod_cast t3) rfl)
  have r9 : ((2 ^ 9 : Nat) : ZMod p) = 512 := by norm_num
  have r8 : ((2 ^ 8 : Nat) : ZMod p) = 256 := by norm_num
  have first := xor_limb_chunks hp (width := 9) (remaining := 7) (by decide) q0 q1
    (x := bdB w limb) (y := bdInitial w limb)
    (z := finalColumn w index 0 2 + ((2 ^ 9 : Nat) : ZMod p) * finalColumn w index 1 2)
    (by rw [r9]; exact b) (by rw [r9]; exact initial) rfl
  have write := final_write index h enabled
  have activeWrite : w (23 + 4 * (limb.val / 2) + limb.val % 2) =
      finalColumn w index 2 2 + ((2 ^ 8 : Nat) : ZMod p) * finalColumn w index 3 2 := by
    have large : ¬ 8 + limb.val < 8 := by omega
    have position : 7 + 4 * ((8 + limb.val) / 2) + (8 + limb.val) % 2 =
        23 + 4 * (limb.val / 2) + limb.val % 2 := by omega
    rw [r8]
    simpa only [index, Fin.val_mk, ite_eq_right large, position] using write
  have second := xor_limb_chunks hp (width := 8) (remaining := 8) (by decide) q2 q3
    (x := bdD w limb)
    (y := finalColumn w index 0 2 + ((2 ^ 9 : Nat) : ZMod p) * finalColumn w index 1 2)
    (by rw [r8]; exact d) (by rw [r8, r9]; exact regroup) activeWrite
  refine ⟨first.2.1, first.1, second.1, second.2.2.1, ?_⟩
  rw [second.2.2.2, first.2.2.2]
  ac_rfl

/-- Uniform statement for every low/high limb of all eight chaining writes. -/
theorem final_limb_xor {p : Nat} [Fact p.Prime] (hp : 65536 ≤ p)
    (compatible : 64 * (-31457280 : ZMod p) = 1) (limb : Fin 16)
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable)) (enabled : w 152 = 1) :
    (w (154 + 4 * (limb.val / 2) + 2 * (limb.val % 2))).val < 65536 ∧
    (w (39 + 4 * (limb.val / 2) + limb.val % 2)).val < 65536 ∧
    (w (71 + 4 * (limb.val / 2) + limb.val % 2)).val < 65536 ∧
    (w (7 + 4 * (limb.val / 2) + limb.val % 2)).val < 65536 ∧
    (w (7 + 4 * (limb.val / 2) + limb.val % 2)).val =
      (w (154 + 4 * (limb.val / 2) + 2 * (limb.val % 2))).val ^^^
      (w (39 + 4 * (limb.val / 2) + limb.val % 2)).val ^^^
      (w (71 + 4 * (limb.val / 2) + limb.val % 2)).val := by
  by_cases small : limb.val < 8
  · exact ac_limb_xor hp compatible ⟨limb.val, small⟩ h enabled
  · have other : limb.val - 8 < 8 := by have := limb.isLt; omega
    have result := bd_limb_xor hp compatible ⟨limb.val - 8, other⟩ h enabled
    have lane : limb.val / 2 = 4 + (limb.val - 8) / 2 := by omega
    have parity : limb.val % 2 = (limb.val - 8) % 2 := by omega
    simpa [bdInitial, bdB, bdD, lane, parity, Nat.mul_add, ← Nat.add_assoc] using result

/-- Word assembly uses the same XOR chunk law as the native lookup proofs. -/
theorem xor_three_words {initial a c output : Word}
    (initialLow : initial.lo < 65536) (aLow : a.lo < 65536) (cLow : c.lo < 65536)
    (low : output.lo = initial.lo ^^^ a.lo ^^^ c.lo)
    (high : output.hi = initial.hi ^^^ a.hi ^^^ c.hi) :
    output.value = initial.value ^^^ a.value ^^^ c.value := by
  have first := xor_of_chunks (width := 16) initialLow aLow
    (a₁ := initial.hi) (b₁ := a.hi)
  have second := xor_of_chunks (width := 16) (Nat.xor_lt_two_pow initialLow aLow) cLow
    (a₁ := initial.hi ^^^ a.hi) (b₁ := c.hi)
  norm_num only [Nat.reducePow] at first second
  simp only [Word.value, limbBase]
  rw [first, second, ← low, ← high]

theorem final_xor_writes {p : Nat} [Fact p.Prime] (hp : 65536 ≤ p)
    (compatible : 64 * (-31457280 : ZMod p) = 1) {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable)) (enabled : w 152 = 1) :
    (Preparation.words w Finalization.stateWrites).map Word.value =
      Vector.ofFn fun i : Fin 8 =>
        (Preparation.words w Variables.chainingInputs)[i].value ^^^
        (Preparation.words w Mixing.extendedWrites)[i.val].value ^^^
        (Preparation.words w Mixing.extendedWrites)[8 + i.val].value := by
  have word (i : Fin 8) :
      (Preparation.words w Finalization.stateWrites)[i].value =
        (Preparation.words w Variables.chainingInputs)[i].value ^^^
        (Preparation.words w Mixing.extendedWrites)[i.val].value ^^^
        (Preparation.words w Mixing.extendedWrites)[8 + i.val].value := by
    have low := final_limb_xor hp compatible
      ⟨2 * i.val, by have := i.isLt; omega⟩ h enabled
    have high := final_limb_xor hp compatible
      ⟨2 * i.val + 1, by have := i.isLt; omega⟩ h enabled
    fin_cases i
    all_goals simp [Preparation.words, Finalization.stateWrites, Variables.chainingInputs,
      Mixing.extendedWrites] at low high ⊢
    all_goals exact xor_three_words low.1 low.2.1 low.2.2.1 low.2.2.2.2 high.2.2.2.2
  apply Vector.ext
  intro i hi
  simpa [Fin.getElem_fin] using word ⟨i, hi⟩

end Airbender.Blake2Round.Proofs
