import Airbender.Review.Helpers.Tables.NativeBinaryRows
import Airbender.Proofs.Tables.PeriodicColumns
import Airbender.Proofs.Tables.ImportedBlocks
import Airbender.Proofs.Tables.LiteralSizes

namespace Airbender.Verification.BinaryProofs
open Setup Setup.Proofs NativeBinary
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

private theorem affine_get (length first step n : Nat) (bound : n < length) :
    Block.get? (.affine length first (step : Int)) n = some (first + step * n) := by
  simp only [Block.get?, Block.length, if_pos bound]
  have casts : (first : Int) + (step : Int) * n = ((first + step * n : Nat) : Int) := by simp
  rw [casts, if_pos (Int.natCast_nonneg _), Int.toNat_natCast]

private theorem single_get (block : Block) (n : Nat) (bound : n < block.length) :
    (⟨#[block]⟩ : Column).get? n = block.get? n := by
  change getFromBlocks [block] n = _
  rw [getFromBlocks, if_pos bound]

theorem first (kind : BinaryKind) (i : Fin 65536) :
    (columns kind)[0].get? i.val = some (i.val / 256) := by
  cases kind <;> change (⟨#[.periodic 256 1 (Array.replicate 256 0)]⟩ : Column).get? i.val = _
  all_goals
    have inside : i.val < 256 * (Array.replicate 256 0).size := by change i.val < 65536; exact i.isLt
    refine (single_get (.periodic 256 1 (Array.replicate 256 0)) i.val inside).trans ?_
    have read := periodic_get (Array.replicate 256 0) 256 1 i.val (by simp only [Array.size_replicate]; decide) inside
    change Block.get? (.periodic 256 1 (Array.replicate 256 0)) i.val = _ at read
    rw [read]
    simp

theorem second (kind : BinaryKind) (i : Fin 65536) :
    (columns kind)[1].get? i.val = some (i.val % 256) := by
  cases kind <;> change (⟨#[.periodic 256 0 (Array.range 256)]⟩ : Column).get? i.val = _
  all_goals
    have inside : i.val < 256 * (Array.range 256).size := by change i.val < 65536; exact i.isLt
    refine (single_get (.periodic 256 0 (Array.range 256)) i.val inside).trans ?_
    have read := periodic_get (Array.range 256) 256 0 i.val (by simp only [Array.size_range]; decide) inside
    change Block.get? (.periodic 256 0 (Array.range 256)) i.val = _ at read
    rw [read]
    simp

theorem tagged (kind : BinaryKind) (i : Fin 65536) :
    (columns kind)[3].get? i.val = some kind.tag := by
  cases kind <;> change (⟨#[.affine 65536 _ 0]⟩ : Column).get? i.val = some _
  all_goals
    rw [single_get _ _ i.isLt]
    simpa [BinaryKind.tag] using affine_get 65536 _ 0 i.val i.isLt

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
/-- Structural length of the actual stored output blocks, without evaluating outputs. -/
theorem coverage (kind : BinaryKind) :
    (((columns kind)[2].blocks.toList).map Block.length).sum = 65536 := by
  cases kind
  all_goals
    dsimp only [columns,dataXor,dataOr,dataAnd,Vector.getElem_mk,
      List.getElem_toArray,List.getElem_cons_zero,List.getElem_cons_succ]
    simp only [raw_toList_append,List.map_append,List.sum_append,List.map_cons,
      List.map_nil,List.sum_cons,List.sum_nil,Block.length,Array.size_ofFn,
      Array.size_replicate,Array.size_range,raw_size_append,raw_literal_size,
      List.length_cons,List.length_nil,Nat.reduceAdd,Nat.reduceMul]

end Airbender.Verification.BinaryProofs
