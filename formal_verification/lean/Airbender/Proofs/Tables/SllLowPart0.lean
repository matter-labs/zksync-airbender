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

theorem outputs_part0 : checkBlocks sllLowHighOutput 0 part0 = true := by
  rw [part0_shape]
  simp only [checkBlocks_cons_iff,checkBlocks_nil,and_true,Block.length,
    Nat.reduceAdd]
  constructor
  · intro i
    have inside := i.isLt
    have value : sllLowHighOutput (0 + i.val) = 0 := by
      by_cases small : i.val < 65536
      · have sh : (0 + i.val) / 65536 = 0 := by omega
        rw [sllLowHighOutput,sh]
        norm_num only
        omega
      · have sh : (0 + i.val) / 65536 = 1 := by omega
        rw [sllLowHighOutput,sh]
        norm_num only
        omega
    rw [value]
    simpa using affine_get 98304 0 0 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (98304 + i.val) / 65536 = 1 := by omega
    have value : ((98304 + i.val) % 65536 * 2 / 65536) % 65536 = 1 := by omega
    rw [sllLowHighOutput,sh]
    norm_num only
    rw [value]
    simpa using affine_get 32768 1 0 i.val inside

end Airbender.Verification.SllLowProofs
