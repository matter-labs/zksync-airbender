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

theorem outputs_part1 : checkBlocks srlHighLowOutput 720897 part1 = true := by
  rw [part1_shape]
  simp only [checkBlocks_cons_iff,checkBlocks_nil,and_true,Block.length,Nat.reduceAdd]
  repeat' apply And.intro
  · intro i
    have inside := i.isLt
    have sh : (720897 + i.val) / 65536 = 11 := by omega
    have value : (((720897 + i.val) % 65536) * 65536 / 2048) % 65536 = 32 + 32 * i.val := by omega
    rw [srlHighLowOutput,sh]
    norm_num only
    rw [value]
    exact affine_get 2047 32 32 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (722944 + i.val) / 65536 = 11 := by omega
    have value : (((722944 + i.val) % 65536) * 65536 / 2048) % 65536 = 0 + 32 * i.val := by omega
    rw [srlHighLowOutput,sh]
    norm_num only
    rw [value]
    exact affine_get 2048 0 32 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (724992 + i.val) / 65536 = 11 := by omega
    have value : (((724992 + i.val) % 65536) * 65536 / 2048) % 65536 = 0 + 32 * i.val := by omega
    rw [srlHighLowOutput,sh]
    norm_num only
    rw [value]
    exact affine_get 2048 0 32 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (727040 + i.val) / 65536 = 11 := by omega
    have value : (((727040 + i.val) % 65536) * 65536 / 2048) % 65536 = 0 + 32 * i.val := by omega
    rw [srlHighLowOutput,sh]
    norm_num only
    rw [value]
    exact affine_get 2048 0 32 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (729088 + i.val) / 65536 = 11 := by omega
    have value : (((729088 + i.val) % 65536) * 65536 / 2048) % 65536 = 0 + 32 * i.val := by omega
    rw [srlHighLowOutput,sh]
    norm_num only
    rw [value]
    exact affine_get 2048 0 32 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (731136 + i.val) / 65536 = 11 := by omega
    have value : (((731136 + i.val) % 65536) * 65536 / 2048) % 65536 = 0 + 32 * i.val := by omega
    rw [srlHighLowOutput,sh]
    norm_num only
    rw [value]
    exact affine_get 2048 0 32 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (733184 + i.val) / 65536 = 11 := by omega
    have value : (((733184 + i.val) % 65536) * 65536 / 2048) % 65536 = 0 + 32 * i.val := by omega
    rw [srlHighLowOutput,sh]
    norm_num only
    rw [value]
    exact affine_get 2048 0 32 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (735232 + i.val) / 65536 = 11 := by omega
    have value : (((735232 + i.val) % 65536) * 65536 / 2048) % 65536 = 0 + 32 * i.val := by omega
    rw [srlHighLowOutput,sh]
    norm_num only
    rw [value]
    exact affine_get 2048 0 32 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (737280 + i.val) / 65536 = 11 := by omega
    have value : (((737280 + i.val) % 65536) * 65536 / 2048) % 65536 = 0 + 32 * i.val := by omega
    rw [srlHighLowOutput,sh]
    norm_num only
    rw [value]
    exact affine_get 2048 0 32 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (739328 + i.val) / 65536 = 11 := by omega
    have value : (((739328 + i.val) % 65536) * 65536 / 2048) % 65536 = 0 + 32 * i.val := by omega
    rw [srlHighLowOutput,sh]
    norm_num only
    rw [value]
    exact affine_get 2048 0 32 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (741376 + i.val) / 65536 = 11 := by omega
    have value : (((741376 + i.val) % 65536) * 65536 / 2048) % 65536 = 0 + 32 * i.val := by omega
    rw [srlHighLowOutput,sh]
    norm_num only
    rw [value]
    exact affine_get 2048 0 32 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (743424 + i.val) / 65536 = 11 := by omega
    have value : (((743424 + i.val) % 65536) * 65536 / 2048) % 65536 = 0 + 32 * i.val := by omega
    rw [srlHighLowOutput,sh]
    norm_num only
    rw [value]
    exact affine_get 2048 0 32 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (745472 + i.val) / 65536 = 11 := by omega
    have value : (((745472 + i.val) % 65536) * 65536 / 2048) % 65536 = 0 + 32 * i.val := by omega
    rw [srlHighLowOutput,sh]
    norm_num only
    rw [value]
    exact affine_get 2048 0 32 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (747520 + i.val) / 65536 = 11 := by omega
    have value : (((747520 + i.val) % 65536) * 65536 / 2048) % 65536 = 0 + 32 * i.val := by omega
    rw [srlHighLowOutput,sh]
    norm_num only
    rw [value]
    exact affine_get 2048 0 32 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (749568 + i.val) / 65536 = 11 := by omega
    have value : (((749568 + i.val) % 65536) * 65536 / 2048) % 65536 = 0 + 32 * i.val := by omega
    rw [srlHighLowOutput,sh]
    norm_num only
    rw [value]
    exact affine_get 2048 0 32 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (751616 + i.val) / 65536 = 11 := by omega
    have value : (((751616 + i.val) % 65536) * 65536 / 2048) % 65536 = 0 + 32 * i.val := by omega
    rw [srlHighLowOutput,sh]
    norm_num only
    rw [value]
    exact affine_get 2048 0 32 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (753664 + i.val) / 65536 = 11 := by omega
    have value : (((753664 + i.val) % 65536) * 65536 / 2048) % 65536 = 0 + 32 * i.val := by omega
    rw [srlHighLowOutput,sh]
    norm_num only
    rw [value]
    exact affine_get 2048 0 32 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (755712 + i.val) / 65536 = 11 := by omega
    have value : (((755712 + i.val) % 65536) * 65536 / 2048) % 65536 = 0 + 32 * i.val := by omega
    rw [srlHighLowOutput,sh]
    norm_num only
    rw [value]
    exact affine_get 2048 0 32 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (757760 + i.val) / 65536 = 11 := by omega
    have value : (((757760 + i.val) % 65536) * 65536 / 2048) % 65536 = 0 + 32 * i.val := by omega
    rw [srlHighLowOutput,sh]
    norm_num only
    rw [value]
    exact affine_get 2048 0 32 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (759808 + i.val) / 65536 = 11 := by omega
    have value : (((759808 + i.val) % 65536) * 65536 / 2048) % 65536 = 0 + 32 * i.val := by omega
    rw [srlHighLowOutput,sh]
    norm_num only
    rw [value]
    exact affine_get 2048 0 32 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (761856 + i.val) / 65536 = 11 := by omega
    have value : (((761856 + i.val) % 65536) * 65536 / 2048) % 65536 = 0 + 32 * i.val := by omega
    rw [srlHighLowOutput,sh]
    norm_num only
    rw [value]
    exact affine_get 2048 0 32 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (763904 + i.val) / 65536 = 11 := by omega
    have value : (((763904 + i.val) % 65536) * 65536 / 2048) % 65536 = 0 + 32 * i.val := by omega
    rw [srlHighLowOutput,sh]
    norm_num only
    rw [value]
    exact affine_get 2048 0 32 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (765952 + i.val) / 65536 = 11 := by omega
    have value : (((765952 + i.val) % 65536) * 65536 / 2048) % 65536 = 0 + 32 * i.val := by omega
    rw [srlHighLowOutput,sh]
    norm_num only
    rw [value]
    exact affine_get 2048 0 32 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (768000 + i.val) / 65536 = 11 := by omega
    have value : (((768000 + i.val) % 65536) * 65536 / 2048) % 65536 = 0 + 32 * i.val := by omega
    rw [srlHighLowOutput,sh]
    norm_num only
    rw [value]
    exact affine_get 2048 0 32 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (770048 + i.val) / 65536 = 11 := by omega
    have value : (((770048 + i.val) % 65536) * 65536 / 2048) % 65536 = 0 + 32 * i.val := by omega
    rw [srlHighLowOutput,sh]
    norm_num only
    rw [value]
    exact affine_get 2048 0 32 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (772096 + i.val) / 65536 = 11 := by omega
    have value : (((772096 + i.val) % 65536) * 65536 / 2048) % 65536 = 0 + 32 * i.val := by omega
    rw [srlHighLowOutput,sh]
    norm_num only
    rw [value]
    exact affine_get 2048 0 32 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (774144 + i.val) / 65536 = 11 := by omega
    have value : (((774144 + i.val) % 65536) * 65536 / 2048) % 65536 = 0 + 32 * i.val := by omega
    rw [srlHighLowOutput,sh]
    norm_num only
    rw [value]
    exact affine_get 2048 0 32 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (776192 + i.val) / 65536 = 11 := by omega
    have value : (((776192 + i.val) % 65536) * 65536 / 2048) % 65536 = 0 + 32 * i.val := by omega
    rw [srlHighLowOutput,sh]
    norm_num only
    rw [value]
    exact affine_get 2048 0 32 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (778240 + i.val) / 65536 = 11 := by omega
    have value : (((778240 + i.val) % 65536) * 65536 / 2048) % 65536 = 0 + 32 * i.val := by omega
    rw [srlHighLowOutput,sh]
    norm_num only
    rw [value]
    exact affine_get 2048 0 32 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (780288 + i.val) / 65536 = 11 := by omega
    have value : (((780288 + i.val) % 65536) * 65536 / 2048) % 65536 = 0 + 32 * i.val := by omega
    rw [srlHighLowOutput,sh]
    norm_num only
    rw [value]
    exact affine_get 2048 0 32 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (782336 + i.val) / 65536 = 11 := by omega
    have value : (((782336 + i.val) % 65536) * 65536 / 2048) % 65536 = 0 + 32 * i.val := by omega
    rw [srlHighLowOutput,sh]
    norm_num only
    rw [value]
    exact affine_get 2048 0 32 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (784384 + i.val) / 65536 = 11 := by omega
    have value : (((784384 + i.val) % 65536) * 65536 / 2048) % 65536 = 0 + 32 * i.val := by omega
    rw [srlHighLowOutput,sh]
    norm_num only
    rw [value]
    exact affine_get 2048 0 32 i.val inside

end Airbender.Verification.SrlHighProofs
