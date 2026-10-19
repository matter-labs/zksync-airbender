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

theorem outputs_part5 : checkBlocks sllHighOutput 1048576 part5 = true := by
  rw [part5_shape]
  simp only [checkBlocks_cons_iff,checkBlocks_nil,and_true,Block.length,
    Nat.reduceAdd]
  · intro i
    have lower : 16 ≤ (1048576 + i.val) / 65536 := by omega
    have upper : (1048576 + i.val) / 65536 < 32 := by have := i.isLt; omega
    have read : Block.get? (.affine 1048576 0 0) i.val = some 0 := by
      simpa using affine_get 1048576 0 0 i.val i.isLt
    interval_cases shift : (1048576 + i.val) / 65536
    all_goals
      rw [sllHighOutput,shift]
      norm_num only
      rw [read]
      congr 1
      omega

end Airbender.Verification.SllHighProofs
