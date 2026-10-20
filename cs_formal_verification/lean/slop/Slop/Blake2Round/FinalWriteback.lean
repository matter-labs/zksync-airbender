import Slop.Blake2Round.FinalXor
import Slop.Blake2Round.OpIndex
import Slop.Blake2G.OpIndex

set_option warningAsError true

namespace Airbender.Blake2Round.Proofs

open Arithmetic Blake2G.Proofs

set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

/-- The selected final-output mux exposes the actual seven/nine- or eight/eight-
    bit assembly. All sixteen state-write equations are checked. -/
theorem final_write {p : Nat} [Fact p.Prime] (limb : Fin 16) {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable)) (enabled : w 152 = 1) :
    w (7 + 4 * (limb.val / 2) + limb.val % 2) =
      w (633 + 7 * limb.val) + (if limb.val < 8 then 128 else 256) * w (634 + 7 * limb.val) := by
  have equation := Verification.assertion_of_holds h
    ⟨153 + 2 * limb.val, by rw [constraint_count]; have := limb.isLt; omega⟩
  fin_cases limb
  all_goals op_index at equation
  all_goals simp [Expression.eval, Verification.environment, enabled] at equation ⊢
  all_goals linear_combination -equation

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
  obtain ⟨q0, q1, q2, q3⟩ := ac_queries compatible limb h
  have inverse : 128 * (-15728640 : ZMod p) = 1 := by linear_combination compatible
  have recover (x low : ZMod p) : x = low + 128 * ((-15728640 : ZMod p) * (x - low)) := by
    linear_combination -(x - low) * inverse
  have first := xor_limb_chunks hp (width := 7) (remaining := 9) (by decide) q0 q1
    (recover _ _) (recover _ _) (zChunks := rfl)
  have write := final_write (limb.castLE (by omega)) h enabled
  have activeWrite : w (7 + 4 * (limb.val / 2) + limb.val % 2) =
      w (633 + 7 * limb.val) + 128 * w (634 + 7 * limb.val) := by
    simpa only [Fin.val_castLE, ite_eq_left limb.isLt] using write
  have second := xor_limb_chunks hp (width := 7) (remaining := 9) (by decide) q2 q3
    (xChunks := rfl) (recover _ _) activeWrite
  refine ⟨first.1, second.2.1, first.2.1, second.2.2.1, ?_⟩
  rw [second.2.2.2, first.2.2.2]
  ac_rfl

-- Actual b/d chunk columns, after the diagonal-lane permutation.
def bdLowB : Vector Nat 8 := #v[625, 627, 493, 495, 537, 539, 581, 583]
def bdHighB : Vector Nat 8 := #v[626, 624, 494, 492, 538, 536, 582, 580]
def bdLowD : Vector Nat 8 := #v[529, 531, 573, 575, 617, 619, 485, 487]
def bdHighD : Vector Nat 8 := #v[530, 528, 574, 572, 618, 616, 486, 484]

def bdInitial {p : Nat} (w : Nat → ZMod p) (limb : Fin 8) : ZMod p :=
  w (170 + 4 * (limb.val / 2) + 2 * (limb.val % 2))
def bdB {p : Nat} (w : Nat → ZMod p) (limb : Fin 8) : ZMod p :=
  w (55 + 4 * (limb.val / 2) + limb.val % 2)
def bdD {p : Nat} (w : Nat → ZMod p) (limb : Fin 8) : ZMod p :=
  w (87 + 4 * (limb.val / 2) + limb.val % 2)

set_option maxHeartbeats 12000000 in
/-- The b/d half changes chunk width between its two XORs. The imported split
    equation, not the witness generator, supplies that change of decomposition. -/
theorem bd_queries {p : Nat} [Fact p.Prime] (hp : 512 ≤ p) (limb : Fin 8)
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable)) :
    chunkXor 9 (w bdLowB[limb]) (w (684 + 7 * limb.val)) (w (685 + 7 * limb.val)) ∧
    chunkXor 7 (w bdHighB[limb])
      ((-3932160 : ZMod p) * (bdInitial w limb - w (684 + 7 * limb.val)))
      (w (686 + 7 * limb.val)) ∧
    chunkXor 8 (w bdLowD[limb]) (w (687 + 7 * limb.val)) (w (689 + 7 * limb.val)) ∧
    chunkXor 8 (w bdHighD[limb]) (2 * w (686 + 7 * limb.val) + w (688 + 7 * limb.val))
      (w (690 + 7 * limb.val)) ∧
    bdB w limb = w bdLowB[limb] + 512 * w bdHighB[limb] ∧
    bdD w limb = w bdLowD[limb] + 256 * w bdHighD[limb] ∧
    w (685 + 7 * limb.val) = w (687 + 7 * limb.val) + 256 * w (688 + 7 * limb.val) := by
  let index : Fin 16 := ⟨8 + limb.val, by have := limb.isLt; omega⟩
  have tag (stage : Fin 4) : finalColumn w index stage 3 =
      ((if stage.val = 0 then 20 else if stage.val = 1 then 19 else 4 : Nat) : ZMod p) := by
    fin_cases limb <;> fin_cases stage <;> simp [index, finalColumn, finalQuery,
      importedConstraints, FlatOperation.lookups, Expression.eval, Verification.environment]
  have q0 := final_query hp index 0 4 h (tag 0)
  have q1 := final_query hp index 1 3 h (tag 1)
  have q2 := final_query hp index 2 0 h (tag 2)
  have q3 := final_query hp index 3 0 h (tag 3)
  have initialHigh : finalColumn w index 1 1 =
      (-3932160 : ZMod p) * (bdInitial w limb - w (684 + 7 * limb.val)) := by
    fin_cases limb
    all_goals simp [index, finalColumn, finalQuery, importedConstraints, FlatOperation.lookups,
      Expression.eval, Verification.environment, bdInitial]
    all_goals ring
  rw [initialHigh] at q1
  have bWrite := Verification.assertion_of_holds h
    ⟨128 + 2 * (limb.val / 2) + limb.val % 2, by rw [constraint_count]; have := limb.isLt; omega⟩
  have dWrite := Verification.assertion_of_holds h
    ⟨144 + 2 * (limb.val / 2) + limb.val % 2, by rw [constraint_count]; have := limb.isLt; omega⟩
  have split := Verification.assertion_of_holds h
    ⟨168 + 2 * limb.val, by rw [constraint_count]; have := limb.isLt; omega⟩
  fin_cases limb
  all_goals simp [index, finalColumn, finalQuery, importedConstraints, FlatOperation.lookups,
    FlatOperation.constraints, Expression.eval, Verification.environment,
    bdInitial, bdB, bdD, bdLowB, bdHighB, bdLowD, bdHighD] at q0 q1 q2 q3 bWrite dWrite split ⊢
  all_goals refine ⟨q0, q1, q2, ?_, ?_, ?_, ?_⟩
  all_goals first
    | simpa [add_comm] using q3
    | linear_combination -bWrite
    | linear_combination -dWrite
    | linear_combination split

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
  obtain ⟨q0, q1, q2, q3, bChunks, dChunks, split⟩ := bd_queries (by omega) limb h
  have inverse : 512 * (-3932160 : ZMod p) = 1 := by linear_combination compatible
  have recover (x low : ZMod p) : x = low + 512 * ((-3932160 : ZMod p) * (x - low)) := by
    linear_combination -(x - low) * inverse
  have first := xor_limb_chunks hp (width := 9) (remaining := 7) (by decide) q0 q1
    bChunks (recover _ _) (zChunks := rfl)
  norm_num only [Nat.reducePow, Nat.cast_ofNat] at first
  have regroup : w (685 + 7 * limb.val) + 512 * w (686 + 7 * limb.val) =
      w (687 + 7 * limb.val) + 256 * (2 * w (686 + 7 * limb.val) + w (688 + 7 * limb.val)) := by
    linear_combination split
  have write := final_write ⟨8 + limb.val, by have := limb.isLt; omega⟩ h enabled
  have activeWrite : w (23 + 4 * (limb.val / 2) + limb.val % 2) =
      w (689 + 7 * limb.val) + 256 * w (690 + 7 * limb.val) := by
    have large : ¬ 8 + limb.val < 8 := by omega
    have index : 7 + 4 * ((8 + limb.val) / 2) + (8 + limb.val) % 2 =
        23 + 4 * (limb.val / 2) + limb.val % 2 := by omega
    have lowIndex : 633 + 7 * (8 + limb.val) = 689 + 7 * limb.val := by omega
    have highIndex : 634 + 7 * (8 + limb.val) = 690 + 7 * limb.val := by omega
    simpa only [Fin.val_mk, ite_eq_right large, index, lowIndex, highIndex] using write
  have second := xor_limb_chunks hp (width := 8) (remaining := 8) (by decide) q2 q3
    dChunks regroup activeWrite
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
