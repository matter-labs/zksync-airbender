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

theorem outputs_part0 : checkBlocks sllHighOutput 0 part0 = true := by
  rw [part0_shape]
  simp only [checkBlocks_cons_iff,checkBlocks_nil,and_true,Block.length,
    Nat.reduceAdd]
  repeat' apply And.intro
  · intro i
    have inside := i.isLt
    have shift : (0 + i.val) / 65536 = 0 := by omega
    have result : (((0 + i.val) % 65536) * 1) % 65536 = 1 * i.val := by omega
    rw [sllHighOutput,shift]
    norm_num only
    rw [result]
    simpa using affine_get 65536 0 1 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (65536 + i.val) / 65536 = 1 := by omega
    have result : (((65536 + i.val) % 65536) * 2) % 65536 = 2 * i.val := by omega
    rw [sllHighOutput,shift]
    norm_num only
    rw [result]
    simpa using affine_get 32768 0 2 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (98304 + i.val) / 65536 = 1 := by omega
    have result : (((98304 + i.val) % 65536) * 2) % 65536 = 2 * i.val := by omega
    rw [sllHighOutput,shift]
    norm_num only
    rw [result]
    simpa using affine_get 32768 0 2 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (131072 + i.val) / 65536 = 2 := by omega
    have result : (((131072 + i.val) % 65536) * 4) % 65536 = 4 * i.val := by omega
    rw [sllHighOutput,shift]
    norm_num only
    rw [result]
    simpa using affine_get 16384 0 4 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (147456 + i.val) / 65536 = 2 := by omega
    have result : (((147456 + i.val) % 65536) * 4) % 65536 = 4 * i.val := by omega
    rw [sllHighOutput,shift]
    norm_num only
    rw [result]
    simpa using affine_get 16384 0 4 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (163840 + i.val) / 65536 = 2 := by omega
    have result : (((163840 + i.val) % 65536) * 4) % 65536 = 4 * i.val := by omega
    rw [sllHighOutput,shift]
    norm_num only
    rw [result]
    simpa using affine_get 16384 0 4 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (180224 + i.val) / 65536 = 2 := by omega
    have result : (((180224 + i.val) % 65536) * 4) % 65536 = 4 * i.val := by omega
    rw [sllHighOutput,shift]
    norm_num only
    rw [result]
    simpa using affine_get 16384 0 4 i.val inside

end Airbender.Verification.SllHighProofs
