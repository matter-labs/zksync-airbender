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

theorem outputs_part2 : checkBlocks sllLowHighOutput 196608 part2 = true := by
  rw [part2_shape]
  simp only [checkBlocks_cons_iff,checkBlocks_nil,and_true,Block.length,
    Nat.reduceAdd]
  repeat' apply And.intro
  · intro i
    have inside := i.isLt
    have sh : (196608 + i.val) / 65536 = 3 := by omega
    have value : (((196608 + i.val) % 65536) * 8 / 65536) % 65536 = 0 := by omega
    rw [sllLowHighOutput,sh]
    norm_num only
    rw [value]
    simpa using affine_get 8192 0 0 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (204800 + i.val) / 65536 = 3 := by omega
    have value : (((204800 + i.val) % 65536) * 8 / 65536) % 65536 = 1 := by omega
    rw [sllLowHighOutput,sh]
    norm_num only
    rw [value]
    simpa using affine_get 8192 1 0 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (212992 + i.val) / 65536 = 3 := by omega
    have value : (((212992 + i.val) % 65536) * 8 / 65536) % 65536 = 2 := by omega
    rw [sllLowHighOutput,sh]
    norm_num only
    rw [value]
    simpa using affine_get 8192 2 0 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (221184 + i.val) / 65536 = 3 := by omega
    have value : (((221184 + i.val) % 65536) * 8 / 65536) % 65536 = 3 := by omega
    rw [sllLowHighOutput,sh]
    norm_num only
    rw [value]
    simpa using affine_get 8192 3 0 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (229376 + i.val) / 65536 = 3 := by omega
    have value : (((229376 + i.val) % 65536) * 8 / 65536) % 65536 = 4 := by omega
    rw [sllLowHighOutput,sh]
    norm_num only
    rw [value]
    simpa using affine_get 8192 4 0 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (237568 + i.val) / 65536 = 3 := by omega
    have value : (((237568 + i.val) % 65536) * 8 / 65536) % 65536 = 5 := by omega
    rw [sllLowHighOutput,sh]
    norm_num only
    rw [value]
    simpa using affine_get 8192 5 0 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (245760 + i.val) / 65536 = 3 := by omega
    have value : (((245760 + i.val) % 65536) * 8 / 65536) % 65536 = 6 := by omega
    rw [sllLowHighOutput,sh]
    norm_num only
    rw [value]
    simpa using affine_get 8192 6 0 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (253952 + i.val) / 65536 = 3 := by omega
    have value : (((253952 + i.val) % 65536) * 8 / 65536) % 65536 = 7 := by omega
    rw [sllLowHighOutput,sh]
    norm_num only
    rw [value]
    simpa using affine_get 8192 7 0 i.val inside

end Airbender.Verification.SllLowProofs
