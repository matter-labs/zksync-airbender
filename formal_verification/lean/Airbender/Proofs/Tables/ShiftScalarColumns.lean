import Airbender.Review.Helpers.Tables.NativeShiftScalarData
import Airbender.Review.Helpers.Tables.ShiftScalars
import Airbender.Proofs.Tables.PeriodicColumns
import Mathlib.Tactic.IntervalCases

namespace Airbender.Verification.ShiftScalarProofs
open Setup Setup.Proofs NativeShiftScalars
set_option warningAsError true
set_option Elab.async false

private theorem affine_get (length first step n : Nat) (bound : n < length) :
    Block.get? (.affine length first (step : Int)) n = some (first + step * n) := by
  simp only [Block.get?, Block.length, if_pos bound]
  have casts : (first : Int) + (step : Int) * n = ((first + step * n : Nat) : Int) := by simp
  rw [casts, if_pos (Int.natCast_nonneg _), Int.toNat_natCast]

private theorem single_get (block : Block) (n : Nat) (bound : n < block.length) :
    (⟨#[block]⟩ : Column).get? n = block.get? n := by
  change getFromBlocks [block] n = _
  rw [getFromBlocks, if_pos bound]

theorem truncate_rows (i : Fin 65536) :
    dataTruncate.rowNat i = (truncateShiftRow i).push 47 := by
  have first : dataTruncate.columns[0].get? i.val = some i.val := by
    change (⟨#[.affine 65536 0 1]⟩ : Column).get? i.val = _
    rw [single_get _ _ i.isLt]
    simpa using affine_get 65536 0 1 i.val i.isLt
  have second : dataTruncate.columns[1].get? i.val = some (i.val % 32) := by
    change (⟨#[.periodic 2048 0 (Array.range 32)]⟩ : Column).get? i.val = _
    have inside : i.val < 2048 * (Array.range 32).size := by change i.val < 65536; exact i.isLt
    rw [single_get _ _ inside]
    simpa using periodic_get (Array.range 32) 2048 0 i.val (by simp) inside
  have zero : dataTruncate.columns[2].get? i.val = some 0 := by
    change (⟨#[.affine 65536 0 0]⟩ : Column).get? i.val = _
    rw [single_get _ _ i.isLt]
    simpa using affine_get 65536 0 0 i.val i.isLt
  have tag : dataTruncate.columns[3].get? i.val = some 47 := by
    change (⟨#[.affine 65536 47 0]⟩ : Column).get? i.val = _
    rw [single_get _ _ i.isLt]
    simpa using affine_get 65536 47 0 i.val i.isLt
  ext lane bound
  interval_cases lane <;> simp [TableData.rowNat,truncateShiftRow,first,second,zero,tag]

theorem range_rows (i : Fin 65536) :
    dataRange.rowNat i = (paddedRangeRow i).push 53 := by
  have read (lane : Fin 4) : dataRange.columns[lane.val].get? i.val =
      some (if lane.val = 0 then i.val else if lane.val = 3 then 53 else 0) := by
    fin_cases lane
    all_goals
      change (⟨#[.affine 65536 _ _]⟩ : Column).get? i.val = _
      rw [single_get _ _ i.isLt]
      first | simpa using affine_get 65536 0 1 i.val i.isLt
            | simpa using affine_get 65536 0 0 i.val i.isLt
            | simpa using affine_get 65536 53 0 i.val i.isLt
  ext lane bound
  have result := congrArg (fun value : Option Nat => value.getD 0) (read ⟨lane,bound⟩)
  interval_cases lane <;> simpa [TableData.rowNat,paddedRangeRow] using result

theorem sign_key (i : Fin 2097152) : dataSignFill.columns[0].get? i.val = some i.val := by
  change (⟨#[.affine 2097152 0 1]⟩ : Column).get? i.val = _
  rw [single_get _ _ i.isLt]
  simpa using affine_get 2097152 0 1 i.val i.isLt

theorem sign_tag (i : Fin 2097152) : dataSignFill.columns[3].get? i.val = some 52 := by
  change (⟨#[.affine 2097152 52 0]⟩ : Column).get? i.val = _
  rw [single_get _ _ i.isLt]
  simpa using affine_get 2097152 52 0 i.val i.isLt

end Airbender.Verification.ShiftScalarProofs
