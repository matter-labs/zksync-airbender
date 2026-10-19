import Airbender.Review.Helpers.Tables.NativeSllHighRows
import Airbender.Proofs.Tables.SllHighParts

namespace Airbender.Verification.SllHighProofs
open Setup Setup.Proofs NativeSllHigh
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

theorem native_zero (i : Fin 2097152) : data.columns[1].get? i.val = some 0 := by
  change (⟨#[.affine 2097152 0 0]⟩ : Column).get? i.val = _
  rw [single_get _ _ i.isLt]
  simpa using affine_get 2097152 0 0 i.val i.isLt

theorem native_tag (i : Fin 2097152) : data.columns[3].get? i.val = some 49 := by
  change (⟨#[.affine 2097152 49 0]⟩ : Column).get? i.val = _
  rw [single_get _ _ i.isLt]
  simpa using affine_get 2097152 49 0 i.val i.isLt

theorem native_output_extent : (data.columns[2].blocks.toList.map Block.length).sum = 2097152 := by
  rw [parts]
  simp only [List.map_append,List.sum_append,part0_extent,part1_extent,part2_extent,
    part3_extent,part4_extent,part5_extent,Nat.reduceAdd]

end Airbender.Verification.SllHighProofs
