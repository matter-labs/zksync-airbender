import Slop.Blake2Round.Soundness.Outputs
import Slop.Blake2Round.OpIndex
import Slop.Blake2G.OpIndex

set_option warningAsError true

namespace Airbender.Blake2Round.Proofs

set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
-- a word range's goals may not use every lemma of the shared simp set
set_option linter.unusedSimpArgs false

/-- Output words 0 to 3 of `extended_writes`. -/
theorem extended_words_0 {p : Nat} [Fact p.Prime] {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable)) (initial : Vector Arithmetic.Word 16)
    (i : Fin 16) (lowerIndex : 0 ≤ i.val) (upperIndex : i.val < 4) :
      (Preparation.words w Mixing.extendedWrites)[i] =
        (phaseUpdate 1 (phaseUpdate 0 initial (columnOutputs w)) (diagonalOutputs w))[i] := by
  have low := Verification.assertion_of_holds h
    ⟨120 + 2 * i.val, by rw [constraint_count]; have size := i.isLt; omega⟩
  have high := Verification.assertion_of_holds h
    ⟨121 + 2 * i.val, by rw [constraint_count]; have size := i.isLt; omega⟩
  fin_cases i
  all_goals op_index at low high
  all_goals try (simp at lowerIndex upperIndex; done)
  all_goals simp [Preparation.words, Mixing.extendedWrites, phaseUpdate, callUpdate,
    callConstants, Specs.BLAKE3.roundConstants, Blake2G.State.Proofs.update,
    columnOutputs, diagonalOutputs, gOutput, columnGAssignment, diagonalGAssignment,
    diagonalGBase, columnGBase, Blake2G.Proofs.assemble, Fin.getElem_fin,
    Arithmetic.Word.mk.injEq]
  all_goals constructor
  all_goals apply congrArg ZMod.val
  all_goals simp only [
    Blake2G.Proofs.assemble,
    Blake2G.Proofs.firstAhi,
    Blake2G.Proofs.firstAlo,
    Blake2G.Proofs.firstChi,
    Blake2G.Proofs.firstClo,
    Blake2G.Proofs.secondAhi,
    Blake2G.Proofs.secondAlo,
    Blake2G.Proofs.secondChi,
    Blake2G.Proofs.secondClo,
    CharP.cast_eq_zero,
    Expression.eval,
    Fin.coe_ofNat_eq_mod,
    Fin.isValue,
    Fin.ofNat_eq_cast,
    Fin.ofNat_self,
    Fin.val_natCast,
    Int.cast_neg,
    Int.cast_ofNat,
    Int.cast_one,
    Int.cast_zero,
    Int.ofNat_eq_natCast,
    Int.reduceNegSucc,
    Nat.cast_ofNat,
    Nat.cast_one,
    Nat.lt_add_one,
    Nat.mod_succ,
    Nat.one_mod,
    Nat.reduceAdd,
    Nat.reduceLT,
    Nat.reduceMod,
    Nat.reduceMul,
    Nat.zero_mod,
    Verification.environment,
    add_zero,
    columnGAssignment,
    columnGBase,
    diagonalGBase,
    mul_neg,
    mul_one,
    mul_zero,
    neg_mul,
    one_mul,
    zero_add,
    ↓reduceIte] at low high ⊢
  all_goals solve
    | linear_combination low
    | linear_combination -low
    | linear_combination high
    | linear_combination -high

end Airbender.Blake2Round.Proofs
