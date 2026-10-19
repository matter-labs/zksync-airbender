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

theorem outputs_part4 : checkBlocks srlHighLowOutput 917504 part4 = true := by
  rw [part4_shape]
  simp only [checkBlocks_cons_iff,checkBlocks_nil,and_true,Block.length,Nat.reduceAdd]
  repeat' apply And.intro
  · intro i
    have inside := i.isLt
    have sh : (917504 + i.val) / 65536 = 14 := by omega
    have value : (((917504 + i.val) % 65536) * 65536 / 16384) % 65536 = 0 + 4 * i.val := by omega
    rw [srlHighLowOutput,sh]
    norm_num only
    rw [value]
    exact affine_get 16384 0 4 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (933888 + i.val) / 65536 = 14 := by omega
    have value : (((933888 + i.val) % 65536) * 65536 / 16384) % 65536 = 0 + 4 * i.val := by omega
    rw [srlHighLowOutput,sh]
    norm_num only
    rw [value]
    exact affine_get 16384 0 4 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (950272 + i.val) / 65536 = 14 := by omega
    have value : (((950272 + i.val) % 65536) * 65536 / 16384) % 65536 = 0 + 4 * i.val := by omega
    rw [srlHighLowOutput,sh]
    norm_num only
    rw [value]
    exact affine_get 16384 0 4 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (966656 + i.val) / 65536 = 14 := by omega
    have value : (((966656 + i.val) % 65536) * 65536 / 16384) % 65536 = 0 + 4 * i.val := by omega
    rw [srlHighLowOutput,sh]
    norm_num only
    rw [value]
    exact affine_get 16384 0 4 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (983040 + i.val) / 65536 = 15 := by omega
    have value : (((983040 + i.val) % 65536) * 65536 / 32768) % 65536 = 0 + 2 * i.val := by omega
    rw [srlHighLowOutput,sh]
    norm_num only
    rw [value]
    exact affine_get 32768 0 2 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (1015808 + i.val) / 65536 = 15 := by omega
    have value : (((1015808 + i.val) % 65536) * 65536 / 32768) % 65536 = 0 + 2 * i.val := by omega
    rw [srlHighLowOutput,sh]
    norm_num only
    rw [value]
    exact affine_get 32768 0 2 i.val inside

end Airbender.Verification.SrlHighProofs
