import Airbender.Review.Helpers.Tables.Shift.ZeroData
import Airbender.Review.Helpers.Tables.Shift.SignData
import Mathlib.Tactic.FinCases

namespace Airbender.Verification.SignColumns
open Setup
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

private theorem constant_get (length value n : Nat) (bound : n < length) :
    Block.get? (.affine length value 0) n = some value := by
  simp [Block.get?, Block.length, bound]

theorem zero_fields (lane : Fin 10) : byteZeroData.columns[lane].get? 0 = some 0 := by
  fin_cases lane <;> decide +kernel

theorem key (n : Nat) (bound : n < 256) : byteSignData.columns[0].get? n = some n := by
  change getFromBlocks [.affine 256 0 1] n = some n
  simp [getFromBlocks, Block.get?, Block.length, bound]

theorem extension (n : Nat) (bound : n < 256) :
    byteSignData.columns[1].get? n = some (if n < 128 then 0 else 255) := by
  change getFromBlocks [.affine 128 0 0, .affine 128 255 0] n = _
  by_cases first : n < 128
  · simp only [getFromBlocks, Block.length, if_pos first]
    exact constant_get _ _ _ first
  · have tail : n - 128 < 128 := by omega
    simp only [getFromBlocks, Block.length, if_neg first, if_pos tail]
    exact constant_get _ _ _ tail

theorem padding (lane : Fin 7) (n : Nat) (bound : n < 256) :
    byteSignData.columns[lane.val + 2].get? n = some 0 := by
  have column : byteSignData.columns[lane.val + 2] = Column.mk #[.affine 256 0 0] := by
    fin_cases lane <;> rfl
  rw [column]
  simp [Column.get?, getFromBlocks, Block.get?, Block.length, bound]

theorem tag (n : Nat) (bound : n < 256) :
    byteSignData.columns[9].get? n = some byteSignDataRegion.id := by
  change (Column.mk #[.affine 256 3 0]).get? n = some 3
  simp [Column.get?, getFromBlocks, Block.get?, Block.length, bound]

end Airbender.Verification.SignColumns
