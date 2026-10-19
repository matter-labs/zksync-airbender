import Airbender.Proofs.Tables.SrlHighParts

namespace Airbender.Verification.SrlHighProofs
open Setup Setup.Proofs NativeSrlHigh
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

private theorem affine_get (length first step n : Nat) (bound : n < length) :
    Block.get? (.affine length first (step : Int)) n = some (first + step * n) := by
  simp only [Block.get?, Block.length, if_pos bound]
  have casts : (first : Int) + (step : Int) * n = ((first + step * n : Nat) : Int) := by simp
  rw [casts, if_pos (Int.natCast_nonneg _), Int.toNat_natCast]

theorem outputs_part2 : checkBlocks srlHighLowOutput 786432 part2 = true := by
  rw [part2_shape]
  simp only [checkBlocks_cons_iff,checkBlocks_nil,and_true,Block.length,Nat.reduceAdd]
  repeat' apply And.intro
  · intro i
    have inside := i.isLt
    have sh : (786432 + i.val) / 65536 = 12 := by omega
    have value : (((786432 + i.val) % 65536) * 65536 / 4096) % 65536 = 0 + 16 * i.val := by omega
    rw [srlHighLowOutput,sh]
    norm_num only
    rw [value]
    exact affine_get 4096 0 16 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (790528 + i.val) / 65536 = 12 := by omega
    have value : (((790528 + i.val) % 65536) * 65536 / 4096) % 65536 = 0 + 16 * i.val := by omega
    rw [srlHighLowOutput,sh]
    norm_num only
    rw [value]
    exact affine_get 4096 0 16 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (794624 + i.val) / 65536 = 12 := by omega
    have value : (((794624 + i.val) % 65536) * 65536 / 4096) % 65536 = 0 + 16 * i.val := by omega
    rw [srlHighLowOutput,sh]
    norm_num only
    rw [value]
    exact affine_get 4096 0 16 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (798720 + i.val) / 65536 = 12 := by omega
    have value : (((798720 + i.val) % 65536) * 65536 / 4096) % 65536 = 0 + 16 * i.val := by omega
    rw [srlHighLowOutput,sh]
    norm_num only
    rw [value]
    exact affine_get 4096 0 16 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (802816 + i.val) / 65536 = 12 := by omega
    have value : (((802816 + i.val) % 65536) * 65536 / 4096) % 65536 = 0 + 16 * i.val := by omega
    rw [srlHighLowOutput,sh]
    norm_num only
    rw [value]
    exact affine_get 4096 0 16 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (806912 + i.val) / 65536 = 12 := by omega
    have value : (((806912 + i.val) % 65536) * 65536 / 4096) % 65536 = 0 + 16 * i.val := by omega
    rw [srlHighLowOutput,sh]
    norm_num only
    rw [value]
    exact affine_get 4096 0 16 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (811008 + i.val) / 65536 = 12 := by omega
    have value : (((811008 + i.val) % 65536) * 65536 / 4096) % 65536 = 0 + 16 * i.val := by omega
    rw [srlHighLowOutput,sh]
    norm_num only
    rw [value]
    exact affine_get 4096 0 16 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (815104 + i.val) / 65536 = 12 := by omega
    have value : (((815104 + i.val) % 65536) * 65536 / 4096) % 65536 = 0 + 16 * i.val := by omega
    rw [srlHighLowOutput,sh]
    norm_num only
    rw [value]
    exact affine_get 4096 0 16 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (819200 + i.val) / 65536 = 12 := by omega
    have value : (((819200 + i.val) % 65536) * 65536 / 4096) % 65536 = 0 + 16 * i.val := by omega
    rw [srlHighLowOutput,sh]
    norm_num only
    rw [value]
    exact affine_get 4096 0 16 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (823296 + i.val) / 65536 = 12 := by omega
    have value : (((823296 + i.val) % 65536) * 65536 / 4096) % 65536 = 0 + 16 * i.val := by omega
    rw [srlHighLowOutput,sh]
    norm_num only
    rw [value]
    exact affine_get 4096 0 16 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (827392 + i.val) / 65536 = 12 := by omega
    have value : (((827392 + i.val) % 65536) * 65536 / 4096) % 65536 = 0 + 16 * i.val := by omega
    rw [srlHighLowOutput,sh]
    norm_num only
    rw [value]
    exact affine_get 4096 0 16 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (831488 + i.val) / 65536 = 12 := by omega
    have value : (((831488 + i.val) % 65536) * 65536 / 4096) % 65536 = 0 + 16 * i.val := by omega
    rw [srlHighLowOutput,sh]
    norm_num only
    rw [value]
    exact affine_get 4096 0 16 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (835584 + i.val) / 65536 = 12 := by omega
    have value : (((835584 + i.val) % 65536) * 65536 / 4096) % 65536 = 0 + 16 * i.val := by omega
    rw [srlHighLowOutput,sh]
    norm_num only
    rw [value]
    exact affine_get 4096 0 16 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (839680 + i.val) / 65536 = 12 := by omega
    have value : (((839680 + i.val) % 65536) * 65536 / 4096) % 65536 = 0 + 16 * i.val := by omega
    rw [srlHighLowOutput,sh]
    norm_num only
    rw [value]
    exact affine_get 4096 0 16 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (843776 + i.val) / 65536 = 12 := by omega
    have value : (((843776 + i.val) % 65536) * 65536 / 4096) % 65536 = 0 + 16 * i.val := by omega
    rw [srlHighLowOutput,sh]
    norm_num only
    rw [value]
    exact affine_get 4096 0 16 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (847872 + i.val) / 65536 = 12 := by omega
    have value : (((847872 + i.val) % 65536) * 65536 / 4096) % 65536 = 0 + 16 * i.val := by omega
    rw [srlHighLowOutput,sh]
    norm_num only
    rw [value]
    exact affine_get 4096 0 16 i.val inside

end Airbender.Verification.SrlHighProofs
