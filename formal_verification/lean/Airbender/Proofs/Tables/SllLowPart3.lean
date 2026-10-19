import Airbender.Proofs.Tables.SllLowParts

namespace Airbender.Verification.SllLowProofs
open Setup Setup.Proofs NativeSllLow
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

private theorem affine_get (length first step n : Nat) (bound : n < length) :
    Block.get? (.affine length first (step : Int)) n = some (first + step * n) := by
  simp only [Block.get?, Block.length, if_pos bound]
  have casts : (first : Int) + (step : Int) * n = ((first + step * n : Nat) : Int) := by simp
  rw [casts, if_pos (Int.natCast_nonneg _), Int.toNat_natCast]

theorem outputs_part3 : checkBlocks sllLowHighOutput 262144 part3 = true := by
  rw [part3_shape]
  simp only [checkBlocks_cons_iff,checkBlocks_nil,and_true,Block.length,
    Nat.reduceAdd]
  repeat' apply And.intro
  · intro i
    have inside := i.isLt
    have sh : (262144 + i.val) / 65536 = 4 := by omega
    have value : (((262144 + i.val) % 65536) * 16 / 65536) % 65536 = 0 := by omega
    rw [sllLowHighOutput,sh]
    norm_num only
    rw [value]
    simpa using affine_get 4096 0 0 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (266240 + i.val) / 65536 = 4 := by omega
    have value : (((266240 + i.val) % 65536) * 16 / 65536) % 65536 = 1 := by omega
    rw [sllLowHighOutput,sh]
    norm_num only
    rw [value]
    simpa using affine_get 4096 1 0 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (270336 + i.val) / 65536 = 4 := by omega
    have value : (((270336 + i.val) % 65536) * 16 / 65536) % 65536 = 2 := by omega
    rw [sllLowHighOutput,sh]
    norm_num only
    rw [value]
    simpa using affine_get 4096 2 0 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (274432 + i.val) / 65536 = 4 := by omega
    have value : (((274432 + i.val) % 65536) * 16 / 65536) % 65536 = 3 := by omega
    rw [sllLowHighOutput,sh]
    norm_num only
    rw [value]
    simpa using affine_get 4096 3 0 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (278528 + i.val) / 65536 = 4 := by omega
    have value : (((278528 + i.val) % 65536) * 16 / 65536) % 65536 = 4 := by omega
    rw [sllLowHighOutput,sh]
    norm_num only
    rw [value]
    simpa using affine_get 4096 4 0 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (282624 + i.val) / 65536 = 4 := by omega
    have value : (((282624 + i.val) % 65536) * 16 / 65536) % 65536 = 5 := by omega
    rw [sllLowHighOutput,sh]
    norm_num only
    rw [value]
    simpa using affine_get 4096 5 0 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (286720 + i.val) / 65536 = 4 := by omega
    have value : (((286720 + i.val) % 65536) * 16 / 65536) % 65536 = 6 := by omega
    rw [sllLowHighOutput,sh]
    norm_num only
    rw [value]
    simpa using affine_get 4096 6 0 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (290816 + i.val) / 65536 = 4 := by omega
    have value : (((290816 + i.val) % 65536) * 16 / 65536) % 65536 = 7 := by omega
    rw [sllLowHighOutput,sh]
    norm_num only
    rw [value]
    simpa using affine_get 4096 7 0 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (294912 + i.val) / 65536 = 4 := by omega
    have value : (((294912 + i.val) % 65536) * 16 / 65536) % 65536 = 8 := by omega
    rw [sllLowHighOutput,sh]
    norm_num only
    rw [value]
    simpa using affine_get 4096 8 0 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (299008 + i.val) / 65536 = 4 := by omega
    have value : (((299008 + i.val) % 65536) * 16 / 65536) % 65536 = 9 := by omega
    rw [sllLowHighOutput,sh]
    norm_num only
    rw [value]
    simpa using affine_get 4096 9 0 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (303104 + i.val) / 65536 = 4 := by omega
    have value : (((303104 + i.val) % 65536) * 16 / 65536) % 65536 = 10 := by omega
    rw [sllLowHighOutput,sh]
    norm_num only
    rw [value]
    simpa using affine_get 4096 10 0 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (307200 + i.val) / 65536 = 4 := by omega
    have value : (((307200 + i.val) % 65536) * 16 / 65536) % 65536 = 11 := by omega
    rw [sllLowHighOutput,sh]
    norm_num only
    rw [value]
    simpa using affine_get 4096 11 0 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (311296 + i.val) / 65536 = 4 := by omega
    have value : (((311296 + i.val) % 65536) * 16 / 65536) % 65536 = 12 := by omega
    rw [sllLowHighOutput,sh]
    norm_num only
    rw [value]
    simpa using affine_get 4096 12 0 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (315392 + i.val) / 65536 = 4 := by omega
    have value : (((315392 + i.val) % 65536) * 16 / 65536) % 65536 = 13 := by omega
    rw [sllLowHighOutput,sh]
    norm_num only
    rw [value]
    simpa using affine_get 4096 13 0 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (319488 + i.val) / 65536 = 4 := by omega
    have value : (((319488 + i.val) % 65536) * 16 / 65536) % 65536 = 14 := by omega
    rw [sllLowHighOutput,sh]
    norm_num only
    rw [value]
    simpa using affine_get 4096 14 0 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (323584 + i.val) / 65536 = 4 := by omega
    have value : (((323584 + i.val) % 65536) * 16 / 65536) % 65536 = 15 := by omega
    rw [sllLowHighOutput,sh]
    norm_num only
    rw [value]
    simpa using affine_get 4096 15 0 i.val inside

end Airbender.Verification.SllLowProofs
