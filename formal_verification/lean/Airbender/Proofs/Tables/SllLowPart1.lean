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

theorem outputs_part1 : checkBlocks sllLowHighOutput 131072 part1 = true := by
  rw [part1_shape]
  simp only [checkBlocks_cons_iff,checkBlocks_nil,and_true,Block.length,
    Nat.reduceAdd]
  repeat' apply And.intro
  · intro i
    have inside := i.isLt
    have sh : (131072 + i.val) / 65536 = 2 := by omega
    have value : (((131072 + i.val) % 65536) * 4 / 65536) % 65536 = 0 := by omega
    rw [sllLowHighOutput,sh]
    norm_num only
    rw [value]
    simpa using affine_get 16384 0 0 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (147456 + i.val) / 65536 = 2 := by omega
    have value : (((147456 + i.val) % 65536) * 4 / 65536) % 65536 = 1 := by omega
    rw [sllLowHighOutput,sh]
    norm_num only
    rw [value]
    simpa using affine_get 16384 1 0 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (163840 + i.val) / 65536 = 2 := by omega
    have value : (((163840 + i.val) % 65536) * 4 / 65536) % 65536 = 2 := by omega
    rw [sllLowHighOutput,sh]
    norm_num only
    rw [value]
    simpa using affine_get 16384 2 0 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (180224 + i.val) / 65536 = 2 := by omega
    have value : (((180224 + i.val) % 65536) * 4 / 65536) % 65536 = 3 := by omega
    rw [sllLowHighOutput,sh]
    norm_num only
    rw [value]
    simpa using affine_get 16384 3 0 i.val inside

end Airbender.Verification.SllLowProofs
