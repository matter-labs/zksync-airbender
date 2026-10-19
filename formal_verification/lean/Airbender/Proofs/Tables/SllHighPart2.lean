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

theorem outputs_part2 : checkBlocks sllHighOutput 262144 part2 = true := by
  rw [part2_shape]
  simp only [checkBlocks_cons_iff,checkBlocks_nil,and_true,Block.length,
    Nat.reduceAdd]
  repeat' apply And.intro
  · intro i
    have inside := i.isLt
    have shift : (262144 + i.val) / 65536 = 4 := by omega
    have result : (((262144 + i.val) % 65536) * 16) % 65536 = 16 * i.val := by omega
    rw [sllHighOutput,shift]
    norm_num only
    rw [result]
    simpa using affine_get 4096 0 16 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (266240 + i.val) / 65536 = 4 := by omega
    have result : (((266240 + i.val) % 65536) * 16) % 65536 = 16 * i.val := by omega
    rw [sllHighOutput,shift]
    norm_num only
    rw [result]
    simpa using affine_get 4096 0 16 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (270336 + i.val) / 65536 = 4 := by omega
    have result : (((270336 + i.val) % 65536) * 16) % 65536 = 16 * i.val := by omega
    rw [sllHighOutput,shift]
    norm_num only
    rw [result]
    simpa using affine_get 4096 0 16 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (274432 + i.val) / 65536 = 4 := by omega
    have result : (((274432 + i.val) % 65536) * 16) % 65536 = 16 * i.val := by omega
    rw [sllHighOutput,shift]
    norm_num only
    rw [result]
    simpa using affine_get 4096 0 16 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (278528 + i.val) / 65536 = 4 := by omega
    have result : (((278528 + i.val) % 65536) * 16) % 65536 = 16 * i.val := by omega
    rw [sllHighOutput,shift]
    norm_num only
    rw [result]
    simpa using affine_get 4096 0 16 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (282624 + i.val) / 65536 = 4 := by omega
    have result : (((282624 + i.val) % 65536) * 16) % 65536 = 16 * i.val := by omega
    rw [sllHighOutput,shift]
    norm_num only
    rw [result]
    simpa using affine_get 4096 0 16 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (286720 + i.val) / 65536 = 4 := by omega
    have result : (((286720 + i.val) % 65536) * 16) % 65536 = 16 * i.val := by omega
    rw [sllHighOutput,shift]
    norm_num only
    rw [result]
    simpa using affine_get 4096 0 16 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (290816 + i.val) / 65536 = 4 := by omega
    have result : (((290816 + i.val) % 65536) * 16) % 65536 = 16 * i.val := by omega
    rw [sllHighOutput,shift]
    norm_num only
    rw [result]
    simpa using affine_get 4096 0 16 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (294912 + i.val) / 65536 = 4 := by omega
    have result : (((294912 + i.val) % 65536) * 16) % 65536 = 16 * i.val := by omega
    rw [sllHighOutput,shift]
    norm_num only
    rw [result]
    simpa using affine_get 4096 0 16 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (299008 + i.val) / 65536 = 4 := by omega
    have result : (((299008 + i.val) % 65536) * 16) % 65536 = 16 * i.val := by omega
    rw [sllHighOutput,shift]
    norm_num only
    rw [result]
    simpa using affine_get 4096 0 16 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (303104 + i.val) / 65536 = 4 := by omega
    have result : (((303104 + i.val) % 65536) * 16) % 65536 = 16 * i.val := by omega
    rw [sllHighOutput,shift]
    norm_num only
    rw [result]
    simpa using affine_get 4096 0 16 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (307200 + i.val) / 65536 = 4 := by omega
    have result : (((307200 + i.val) % 65536) * 16) % 65536 = 16 * i.val := by omega
    rw [sllHighOutput,shift]
    norm_num only
    rw [result]
    simpa using affine_get 4096 0 16 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (311296 + i.val) / 65536 = 4 := by omega
    have result : (((311296 + i.val) % 65536) * 16) % 65536 = 16 * i.val := by omega
    rw [sllHighOutput,shift]
    norm_num only
    rw [result]
    simpa using affine_get 4096 0 16 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (315392 + i.val) / 65536 = 4 := by omega
    have result : (((315392 + i.val) % 65536) * 16) % 65536 = 16 * i.val := by omega
    rw [sllHighOutput,shift]
    norm_num only
    rw [result]
    simpa using affine_get 4096 0 16 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (319488 + i.val) / 65536 = 4 := by omega
    have result : (((319488 + i.val) % 65536) * 16) % 65536 = 16 * i.val := by omega
    rw [sllHighOutput,shift]
    norm_num only
    rw [result]
    simpa using affine_get 4096 0 16 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (323584 + i.val) / 65536 = 4 := by omega
    have result : (((323584 + i.val) % 65536) * 16) % 65536 = 16 * i.val := by omega
    rw [sllHighOutput,shift]
    norm_num only
    rw [result]
    simpa using affine_get 4096 0 16 i.val inside

end Airbender.Verification.SllHighProofs
