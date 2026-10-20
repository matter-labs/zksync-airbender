import Slop.Blake2Round.Soundness.Outputs

set_option warningAsError true

namespace Airbender.Blake2Round.Proofs

set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
-- a word range's goals may not use every lemma of the shared simp set
set_option linter.unusedSimpArgs false

/-- Output words 12 to 15 of `extended_writes`. -/
theorem extended_words_3 {p : Nat} [Fact p.Prime] {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable)) (initial : Vector Arithmetic.Word 16)
    (i : Fin 16) (lowerIndex : 12 ≤ i.val) (upperIndex : i.val < 16) :
      (Preparation.words w Mixing.extendedWrites)[i] =
        (phaseUpdate 1 (phaseUpdate 0 initial (columnOutputs w)) (diagonalOutputs w))[i] := by
  have low := Verification.assertion_of_holds h
    ⟨120 + 2 * i.val, by rw [constraint_count]; have size := i.isLt; omega⟩
  have high := Verification.assertion_of_holds h
    ⟨121 + 2 * i.val, by rw [constraint_count]; have size := i.isLt; omega⟩
  fin_cases i
  all_goals try (simp at lowerIndex upperIndex; done)
  all_goals simp [Preparation.words, Mixing.extendedWrites, phaseUpdate, callUpdate,
    callConstants, Specs.BLAKE3.roundConstants, Blake2G.State.Proofs.update,
    columnOutputs, diagonalOutputs, gOutput, columnGAssignment, diagonalGAssignment,
    diagonalGBase, columnGBase, Blake2G.Proofs.assemble, Fin.getElem_fin,
    Arithmetic.Word.mk.injEq]
  all_goals constructor
  all_goals apply congrArg ZMod.val
  all_goals simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment, Blake2G.Proofs.secondAlo, Blake2G.Proofs.secondAhi,
    Blake2G.Proofs.secondClo, Blake2G.Proofs.secondChi, Blake2G.Proofs.firstAlo,
    Blake2G.Proofs.firstAhi, Blake2G.Proofs.firstClo, Blake2G.Proofs.firstChi,
    diagonalGBase, columnGAssignment, columnGBase, Blake2G.Proofs.assemble] at low high ⊢
  all_goals solve
    | linear_combination low
    | linear_combination -low
    | linear_combination high
    | linear_combination -high

end Airbender.Blake2Round.Proofs
