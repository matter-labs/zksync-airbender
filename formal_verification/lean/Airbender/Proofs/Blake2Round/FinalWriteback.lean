import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Review.Helpers.Core.SerializedInverse
import Airbender.Review.Circuits.Blake2Round.Finalization
import Airbender.Proofs.Blake2Round.NativeFinalQueries

set_option warningAsError true

namespace Airbender.Blake2Round.Proofs
open Arithmetic Blake2G.Proofs
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

/-- Active finalization exposes the native seven/nine- or eight/eight-bit assembly. -/
theorem final_write {p : Nat} [Fact p.Prime] (limb : Fin 16) {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable)) (enabled : w 152 = 1) :
    NativeFinalLayout.stateWrite w limb = NativeFinalLayout.temporary w limb 4 +
      (if limb.val < 8 then 128 else 256) * NativeFinalLayout.temporary w limb 5 :=
  native_final_active_write limb h enabled

/-- The a/c half of finalization needs no external limb bounds: the four
    imported queries bound and identify each of its three XOR inputs. -/
theorem ac_limb_xor {p : Nat} [Fact p.Prime] (hp : FieldCapacity.AtLeast p 65536)
    (compatible : SerializedInverse.Scale64 p) (limb : Fin 8)
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable)) (enabled : w 152 = 1) :
    (acInitial w limb).val < 65536 ∧ (acA w limb).val < 65536 ∧
    (acC w limb).val < 65536 ∧
    (w (7 + 4 * (limb.val / 2) + limb.val % 2)).val < 65536 ∧
    (w (7 + 4 * (limb.val / 2) + limb.val % 2)).val =
      (acInitial w limb).val ^^^ (acA w limb).val ^^^ (acC w limb).val := by
  obtain ⟨q0, q1, q2, q3⟩ := ac_queries compatible limb h
  have inverse : SerializedInverse.Scale128 p := by linear_combination compatible
  have recover (x low : ZMod p) : x = low + 128 * ((-15728640 : ZMod p) * (x - low)) := by
    linear_combination -(x - low) * inverse
  have first := xor_limb_chunks hp (width := 7) (remaining := 9) (by decide) q0 q1
    (recover _ _) (recover _ _) (zChunks := rfl)
  have write := final_write (limb.castLE (by omega)) h enabled
  have activeWrite : w (7 + 4 * (limb.val / 2) + limb.val % 2) =
      acTemp w limb 4 + 128 * acTemp w limb 5 := by
    simpa [NativeFinalLayout.stateWrite, NativeFinalLayout.temporary, acTemp, limb.isLt] using write
  have second := xor_limb_chunks hp (width := 7) (remaining := 9) (by decide) q2 q3
    (xChunks := rfl) (recover _ _) activeWrite
  refine ⟨first.1, second.2.1, first.2.1, second.2.2.1, ?_⟩
  rw [second.2.2.2, first.2.2.2]
  ac_rfl

/-- Both XOR decompositions come from native queries. The width change is
    an algebraic regrouping of the optimized expression. -/
theorem bd_limb_xor {p : Nat} [Fact p.Prime] (hp : FieldCapacity.AtLeast p 65536)
    (compatible : SerializedInverse.Scale64 p) (limb : Fin 8)
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable)) (enabled : w 152 = 1) :
    (bdInitial w limb).val < 65536 ∧ (bdB w limb).val < 65536 ∧
    (bdD w limb).val < 65536 ∧
    (w (23 + 4 * (limb.val / 2) + limb.val % 2)).val < 65536 ∧
    (w (23 + 4 * (limb.val / 2) + limb.val % 2)).val =
      (bdInitial w limb).val ^^^ (bdB w limb).val ^^^ (bdD w limb).val := by
  obtain ⟨q0, q1, q2, q3⟩ := bd_queries compatible limb h
  have inverse9 : SerializedInverse.Scale512 p := by linear_combination compatible
  have inverse8 : SerializedInverse.Scale256 p := by linear_combination compatible
  have recover9 (x low : ZMod p) : x = low + 512 * ((-3932160 : ZMod p) * (x - low)) := by
    linear_combination -(x - low) * inverse9
  have bChunks : bdB w limb = bdLowB w limb + 512 * bdHighB w limb := recover9 _ _
  have dChunks : bdD w limb = bdLowD w limb + 256 * bdHighD w limb := by
    dsimp [bdHighD]
    linear_combination -(bdD w limb - bdLowD w limb) * inverse8
  have first := xor_limb_chunks hp (width := 9) (remaining := 7) (by decide) q0 q1
    bChunks (recover9 _ _) (zChunks := rfl)
  norm_num only [Nat.reducePow, Nat.cast_ofNat] at first
  have regroup : bdTemp w limb 1 + 512 * bdTemp w limb 2 =
      (bdTemp w limb 1 - 256 * bdTemp w limb 3) +
        256 * (2 * bdTemp w limb 2 + bdTemp w limb 3) := by ring
  have write := final_write (bdIndex limb) h enabled
  have activeWrite : w (23 + 4 * (limb.val / 2) + limb.val % 2) =
      bdTemp w limb 4 + 256 * bdTemp w limb 5 := by
    fin_cases limb
    all_goals simpa [NativeFinalLayout.stateWrite, NativeFinalLayout.temporary, bdTemp, bdIndex] using write
  have second := xor_limb_chunks hp (width := 8) (remaining := 8) (by decide) q2 q3
    dChunks regroup activeWrite
  refine ⟨first.2.1, first.1, second.1, second.2.2.1, ?_⟩
  rw [second.2.2.2, first.2.2.2]
  ac_rfl

/-- Uniform statement for every low/high limb of all eight chaining writes. -/
theorem final_limb_xor {p : Nat} [Fact p.Prime] (hp : FieldCapacity.AtLeast p 65536)
    (compatible : SerializedInverse.Scale64 p) (limb : Fin 16)
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
  fin_cases limb
  · simpa [acInitial, acA, acC, bdInitial, bdB, bdD, bdIndex,
      NativeFinalLayout.initial, NativeFinalLayout.firstInput, NativeFinalLayout.secondInput]
      using ac_limb_xor hp compatible 0 h enabled
  · simpa [acInitial, acA, acC, bdInitial, bdB, bdD, bdIndex,
      NativeFinalLayout.initial, NativeFinalLayout.firstInput, NativeFinalLayout.secondInput]
      using ac_limb_xor hp compatible 1 h enabled
  · simpa [acInitial, acA, acC, bdInitial, bdB, bdD, bdIndex,
      NativeFinalLayout.initial, NativeFinalLayout.firstInput, NativeFinalLayout.secondInput]
      using ac_limb_xor hp compatible 2 h enabled
  · simpa [acInitial, acA, acC, bdInitial, bdB, bdD, bdIndex,
      NativeFinalLayout.initial, NativeFinalLayout.firstInput, NativeFinalLayout.secondInput]
      using ac_limb_xor hp compatible 3 h enabled
  · simpa [acInitial, acA, acC, bdInitial, bdB, bdD, bdIndex,
      NativeFinalLayout.initial, NativeFinalLayout.firstInput, NativeFinalLayout.secondInput]
      using ac_limb_xor hp compatible 4 h enabled
  · simpa [acInitial, acA, acC, bdInitial, bdB, bdD, bdIndex,
      NativeFinalLayout.initial, NativeFinalLayout.firstInput, NativeFinalLayout.secondInput]
      using ac_limb_xor hp compatible 5 h enabled
  · simpa [acInitial, acA, acC, bdInitial, bdB, bdD, bdIndex,
      NativeFinalLayout.initial, NativeFinalLayout.firstInput, NativeFinalLayout.secondInput]
      using ac_limb_xor hp compatible 6 h enabled
  · simpa [acInitial, acA, acC, bdInitial, bdB, bdD, bdIndex,
      NativeFinalLayout.initial, NativeFinalLayout.firstInput, NativeFinalLayout.secondInput]
      using ac_limb_xor hp compatible 7 h enabled
  · simpa [acInitial, acA, acC, bdInitial, bdB, bdD, bdIndex,
      NativeFinalLayout.initial, NativeFinalLayout.firstInput, NativeFinalLayout.secondInput]
      using bd_limb_xor hp compatible 0 h enabled
  · simpa [acInitial, acA, acC, bdInitial, bdB, bdD, bdIndex,
      NativeFinalLayout.initial, NativeFinalLayout.firstInput, NativeFinalLayout.secondInput]
      using bd_limb_xor hp compatible 1 h enabled
  · simpa [acInitial, acA, acC, bdInitial, bdB, bdD, bdIndex,
      NativeFinalLayout.initial, NativeFinalLayout.firstInput, NativeFinalLayout.secondInput]
      using bd_limb_xor hp compatible 2 h enabled
  · simpa [acInitial, acA, acC, bdInitial, bdB, bdD, bdIndex,
      NativeFinalLayout.initial, NativeFinalLayout.firstInput, NativeFinalLayout.secondInput]
      using bd_limb_xor hp compatible 3 h enabled
  · simpa [acInitial, acA, acC, bdInitial, bdB, bdD, bdIndex,
      NativeFinalLayout.initial, NativeFinalLayout.firstInput, NativeFinalLayout.secondInput]
      using bd_limb_xor hp compatible 4 h enabled
  · simpa [acInitial, acA, acC, bdInitial, bdB, bdD, bdIndex,
      NativeFinalLayout.initial, NativeFinalLayout.firstInput, NativeFinalLayout.secondInput]
      using bd_limb_xor hp compatible 5 h enabled
  · simpa [acInitial, acA, acC, bdInitial, bdB, bdD, bdIndex,
      NativeFinalLayout.initial, NativeFinalLayout.firstInput, NativeFinalLayout.secondInput]
      using bd_limb_xor hp compatible 6 h enabled
  · simpa [acInitial, acA, acC, bdInitial, bdB, bdD, bdIndex,
      NativeFinalLayout.initial, NativeFinalLayout.firstInput, NativeFinalLayout.secondInput]
      using bd_limb_xor hp compatible 7 h enabled

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

theorem final_xor_writes {p : Nat} [Fact p.Prime] (hp : FieldCapacity.AtLeast p 65536)
    (compatible : SerializedInverse.Scale64 p) {w : Nat → ZMod p}
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
