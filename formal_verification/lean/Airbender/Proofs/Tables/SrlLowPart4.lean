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

theorem outputs_part4 : checkBlocks srlLowOutput 917504 part4 = true := by
  rw [part4_shape]
  simp only [checkBlocks_cons_iff,checkBlocks_nil,and_true,Block.length,
    Nat.reduceAdd]
  repeat' apply And.intro
  · intro i
    have inside := i.isLt
    have shift : (917504 + i.val) / 65536 = 14 := by omega
    have quotient : ((917504 + i.val) % 65536) / 16384 = 0 := by omega
    rw [srlLowOutput,shift]
    norm_num only
    rw [quotient]
    simpa using affine_get 16384 0 0 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (933888 + i.val) / 65536 = 14 := by omega
    have quotient : ((933888 + i.val) % 65536) / 16384 = 1 := by omega
    rw [srlLowOutput,shift]
    norm_num only
    rw [quotient]
    simpa using affine_get 16384 1 0 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (950272 + i.val) / 65536 = 14 := by omega
    have quotient : ((950272 + i.val) % 65536) / 16384 = 2 := by omega
    rw [srlLowOutput,shift]
    norm_num only
    rw [quotient]
    simpa using affine_get 16384 2 0 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (966656 + i.val) / 65536 = 14 := by omega
    have quotient : ((966656 + i.val) % 65536) / 16384 = 3 := by omega
    rw [srlLowOutput,shift]
    norm_num only
    rw [quotient]
    simpa using affine_get 16384 3 0 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (983040 + i.val) / 65536 = 15 := by omega
    have quotient : ((983040 + i.val) % 65536) / 32768 = 0 := by omega
    rw [srlLowOutput,shift]
    norm_num only
    rw [quotient]
    simpa using affine_get 32768 0 0 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (1015808 + i.val) / 65536 = 15 := by omega
    have quotient : ((1015808 + i.val) % 65536) / 32768 = 1 := by omega
    rw [srlLowOutput,shift]
    norm_num only
    rw [quotient]
    simpa using affine_get 32768 1 0 i.val inside

end Airbender.Verification.SrlLowProofs
