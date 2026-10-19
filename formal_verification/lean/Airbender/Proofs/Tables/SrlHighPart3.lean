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

theorem outputs_part3 : checkBlocks srlHighLowOutput 851968 part3 = true := by
  rw [part3_shape]
  simp only [checkBlocks_cons_iff,checkBlocks_nil,and_true,Block.length,Nat.reduceAdd]
  repeat' apply And.intro
  · intro i
    have inside := i.isLt
    have sh : (851968 + i.val) / 65536 = 13 := by omega
    have value : (((851968 + i.val) % 65536) * 65536 / 8192) % 65536 = 0 + 8 * i.val := by omega
    rw [srlHighLowOutput,sh]
    norm_num only
    rw [value]
    exact affine_get 8192 0 8 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (860160 + i.val) / 65536 = 13 := by omega
    have value : (((860160 + i.val) % 65536) * 65536 / 8192) % 65536 = 0 + 8 * i.val := by omega
    rw [srlHighLowOutput,sh]
    norm_num only
    rw [value]
    exact affine_get 8192 0 8 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (868352 + i.val) / 65536 = 13 := by omega
    have value : (((868352 + i.val) % 65536) * 65536 / 8192) % 65536 = 0 + 8 * i.val := by omega
    rw [srlHighLowOutput,sh]
    norm_num only
    rw [value]
    exact affine_get 8192 0 8 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (876544 + i.val) / 65536 = 13 := by omega
    have value : (((876544 + i.val) % 65536) * 65536 / 8192) % 65536 = 0 + 8 * i.val := by omega
    rw [srlHighLowOutput,sh]
    norm_num only
    rw [value]
    exact affine_get 8192 0 8 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (884736 + i.val) / 65536 = 13 := by omega
    have value : (((884736 + i.val) % 65536) * 65536 / 8192) % 65536 = 0 + 8 * i.val := by omega
    rw [srlHighLowOutput,sh]
    norm_num only
    rw [value]
    exact affine_get 8192 0 8 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (892928 + i.val) / 65536 = 13 := by omega
    have value : (((892928 + i.val) % 65536) * 65536 / 8192) % 65536 = 0 + 8 * i.val := by omega
    rw [srlHighLowOutput,sh]
    norm_num only
    rw [value]
    exact affine_get 8192 0 8 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (901120 + i.val) / 65536 = 13 := by omega
    have value : (((901120 + i.val) % 65536) * 65536 / 8192) % 65536 = 0 + 8 * i.val := by omega
    rw [srlHighLowOutput,sh]
    norm_num only
    rw [value]
    exact affine_get 8192 0 8 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (909312 + i.val) / 65536 = 13 := by omega
    have value : (((909312 + i.val) % 65536) * 65536 / 8192) % 65536 = 0 + 8 * i.val := by omega
    rw [srlHighLowOutput,sh]
    norm_num only
    rw [value]
    exact affine_get 8192 0 8 i.val inside

end Airbender.Verification.SrlHighProofs
