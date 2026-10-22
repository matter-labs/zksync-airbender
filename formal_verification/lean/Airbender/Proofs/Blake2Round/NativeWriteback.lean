import Airbender.Review.Helpers.Core.SerializedInverse
import Airbender.Proofs.Blake2Round.NativeWritebackPart0
import Airbender.Proofs.Blake2Round.NativeWritebackPart1
import Airbender.Proofs.Blake2Round.NativeWritebackPart2
import Airbender.Proofs.Blake2Round.NativeWritebackPart3

namespace Airbender.Blake2Round.Proofs
set_option warningAsError true
set_option Elab.async false
/-- The native writeback is assembled from the checked limb projections. -/
theorem extended_writes {p : Nat} [Fact p.Prime]
    (compatible : SerializedInverse.Scale64 p)
    (w : Nat → ZMod p) (initial : Vector Arithmetic.Word 16) :
    Preparation.words w Mixing.extendedWrites =
      phaseUpdate 1 (phaseUpdate 0 initial (columnOutputs w)) (diagonalOutputs w) := by
  apply Vector.ext
  intro i hi
  have word (j : Fin 16) :
      (Preparation.words w Mixing.extendedWrites)[j] =
        (phaseUpdate 1 (phaseUpdate 0 initial (columnOutputs w)) (diagonalOutputs w))[j] := by
    fin_cases j
    · exact native_writeback_part_0 compatible w initial 0
    · exact native_writeback_part_0 compatible w initial 1
    · exact native_writeback_part_0 compatible w initial 2
    · exact native_writeback_part_0 compatible w initial 3
    · exact native_writeback_part_1 compatible w initial 0
    · exact native_writeback_part_1 compatible w initial 1
    · exact native_writeback_part_1 compatible w initial 2
    · exact native_writeback_part_1 compatible w initial 3
    · exact native_writeback_part_2 compatible w initial 0
    · exact native_writeback_part_2 compatible w initial 1
    · exact native_writeback_part_2 compatible w initial 2
    · exact native_writeback_part_2 compatible w initial 3
    · exact native_writeback_part_3 compatible w initial 0
    · exact native_writeback_part_3 compatible w initial 1
    · exact native_writeback_part_3 compatible w initial 2
    · exact native_writeback_part_3 compatible w initial 3
  exact word ⟨i, hi⟩

end Airbender.Blake2Round.Proofs
