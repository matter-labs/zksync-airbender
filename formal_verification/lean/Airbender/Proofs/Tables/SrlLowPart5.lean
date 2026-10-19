import Airbender.Proofs.Tables.SrlLowParts

namespace Airbender.Verification.SrlLowProofs
open Setup Setup.Proofs NativeSrlLow
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

private theorem affine_get (length first step n : Nat) (bound : n < length) :
    Block.get? (.affine length first (step : Int)) n = some (first + step * n) := by
  simp only [Block.get?, Block.length, if_pos bound]
  have casts : (first : Int) + (step : Int) * n = ((first + step * n : Nat) : Int) := by simp
  rw [casts, if_pos (Int.natCast_nonneg _), Int.toNat_natCast]

theorem outputs_part5 : checkBlocks srlLowOutput 1048576 part5 = true := by
  rw [part5_shape]
  simp only [checkBlocks_cons_iff,checkBlocks_nil,and_true,Block.length]
  · intro i
    have lower : 16 ≤ (1048576 + i.val) / 65536 := by omega
    have upper : (1048576 + i.val) / 65536 < 32 := by have := i.isLt; omega
    interval_cases shift : (1048576 + i.val) / 65536
    all_goals
      rw [srlLowOutput,shift]
      norm_num only
      have remainder : (1048576 + i.val) % 65536 < 65536 := Nat.mod_lt _ (by decide)
      rw [Nat.div_eq_of_lt (by omega)]
      simpa using affine_get 1048576 0 0 i.val i.isLt

end Airbender.Verification.SrlLowProofs
