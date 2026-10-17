import Airbender.Import.Setup
import Mathlib.Tactic.Ring

namespace Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false

/-- Equal affine starts and strides identify every value in an overlap, even
    for negative strides. Bounds only select existing source/slice rows. -/
theorem affine_overlap (leftLength rightLength first other sourceRow sliceRow row : Nat)
    (step : Int)
    (start : (first : Int) + step * sourceRow = (other : Int) + step * sliceRow)
    (left : sourceRow + row < leftLength) (right : sliceRow + row < rightLength) :
    (Block.affine leftLength first step).get? (sourceRow + row) =
      (Block.affine rightLength other step).get? (sliceRow + row) := by
  have equal : (first : Int) + step * (sourceRow + row) =
      (other : Int) + step * (sliceRow + row) := by
    calc
      _ = ((first : Int) + step * sourceRow) + step * row := by ring
      _ = ((other : Int) + step * sliceRow) + step * row := by rw [start]
      _ = _ := by ring
  simp only [Block.get?, Block.length, if_pos left, if_pos right, Int.natCast_add, equal]

end Airbender.Setup.Proofs
