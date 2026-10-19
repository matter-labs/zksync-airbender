import Airbender.Review.Helpers.Tables.NativeSllLowRows
import Airbender.Proofs.Tables.SllLowParts

namespace Airbender.Verification.SllLowProofs
open Setup Setup.Proofs NativeSllLow
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

theorem native_key (i : Fin 2097152) : data.columns[0].get? i.val = some i.val := by
  change (⟨#[.affine 2097152 0 1]⟩ : Column).get? i.val = _
  rw [single_get _ _ i.isLt]
  simpa using affine_get 2097152 0 1 i.val i.isLt

private theorem column_eq (left right : Column)
    (same : left.blocks.toList = right.blocks.toList) : left = right := by
  cases left with
  | mk leftArray =>
    cases right with
    | mk rightArray =>
      have arrays : leftArray = rightArray := by
        simpa only [Array.toArray_toList] using congrArg List.toArray same
      exact congrArg Column.mk arrays

theorem native_low_column : data.columns[1] = NativeSllHigh.data.columns[2] := by
  apply column_eq
  dsimp only [data,NativeSllHigh.data,Vector.getElem_mk,Fin.getElem_fin,
    List.getElem_toArray,List.getElem_cons_zero,List.getElem_cons_succ]

theorem native_low (i : Fin 2097152) :
    data.columns[1].get? i.val = some (sllHighOutput i.val) := by
  rw [native_low_column]
  exact SllHighProofs.native_output i

theorem native_tag (i : Fin 2097152) : data.columns[3].get? i.val = some 48 := by
  change (⟨#[.affine 2097152 48 0]⟩ : Column).get? i.val = _
  rw [single_get _ _ i.isLt]
  simpa using affine_get 2097152 48 0 i.val i.isLt

theorem native_high_extent : (data.columns[2].blocks.toList.map Block.length).sum = 2097152 := by
  rw [native_high_shape]
  simp only [List.map_append,List.sum_append,prefix_extent,SllHighProofs.part0_extent,
    SllHighProofs.part1_extent,SllHighProofs.part2_extent,SllHighProofs.part3_extent,
    SllHighProofs.part4_extent,Nat.reduceAdd]

end Airbender.Verification.SllLowProofs
