import Airbender.Proofs.Tables.SllHighParts

namespace Airbender.Verification.SllHighProofs
open Setup Setup.Proofs NativeSllHigh
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

private theorem affine_get (length first step n : Nat) (bound : n < length) :
    Block.get? (.affine length first (step : Int)) n = some (first + step * n) := by
  simp only [Block.get?, Block.length, if_pos bound]
  have casts : (first : Int) + (step : Int) * n = ((first + step * n : Nat) : Int) := by simp
  rw [casts, if_pos (Int.natCast_nonneg _), Int.toNat_natCast]

theorem outputs_part1 : checkBlocks sllHighOutput 196608 part1 = true := by
  rw [part1_shape]
  simp only [checkBlocks_cons_iff,checkBlocks_nil,and_true,Block.length,
    Nat.reduceAdd]
  repeat' apply And.intro
  · intro i
    have inside := i.isLt
    have shift : (196608 + i.val) / 65536 = 3 := by omega
    have result : (((196608 + i.val) % 65536) * 8) % 65536 = 8 * i.val := by omega
    rw [sllHighOutput,shift]
    norm_num only
    rw [result]
    simpa using affine_get 8192 0 8 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (204800 + i.val) / 65536 = 3 := by omega
    have result : (((204800 + i.val) % 65536) * 8) % 65536 = 8 * i.val := by omega
    rw [sllHighOutput,shift]
    norm_num only
    rw [result]
    simpa using affine_get 8192 0 8 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (212992 + i.val) / 65536 = 3 := by omega
    have result : (((212992 + i.val) % 65536) * 8) % 65536 = 8 * i.val := by omega
    rw [sllHighOutput,shift]
    norm_num only
    rw [result]
    simpa using affine_get 8192 0 8 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (221184 + i.val) / 65536 = 3 := by omega
    have result : (((221184 + i.val) % 65536) * 8) % 65536 = 8 * i.val := by omega
    rw [sllHighOutput,shift]
    norm_num only
    rw [result]
    simpa using affine_get 8192 0 8 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (229376 + i.val) / 65536 = 3 := by omega
    have result : (((229376 + i.val) % 65536) * 8) % 65536 = 8 * i.val := by omega
    rw [sllHighOutput,shift]
    norm_num only
    rw [result]
    simpa using affine_get 8192 0 8 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (237568 + i.val) / 65536 = 3 := by omega
    have result : (((237568 + i.val) % 65536) * 8) % 65536 = 8 * i.val := by omega
    rw [sllHighOutput,shift]
    norm_num only
    rw [result]
    simpa using affine_get 8192 0 8 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (245760 + i.val) / 65536 = 3 := by omega
    have result : (((245760 + i.val) % 65536) * 8) % 65536 = 8 * i.val := by omega
    rw [sllHighOutput,shift]
    norm_num only
    rw [result]
    simpa using affine_get 8192 0 8 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (253952 + i.val) / 65536 = 3 := by omega
    have result : (((253952 + i.val) % 65536) * 8) % 65536 = 8 * i.val := by omega
    rw [sllHighOutput,shift]
    norm_num only
    rw [result]
    simpa using affine_get 8192 0 8 i.val inside

end Airbender.Verification.SllHighProofs
