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

theorem outputs_part3 : checkBlocks srlLowOutput 851968 part3 = true := by
  rw [part3_shape]
  simp only [checkBlocks_cons_iff,checkBlocks_nil,and_true,Block.length,
    Nat.reduceAdd]
  repeat' apply And.intro
  · intro i
    have inside := i.isLt
    have shift : (851968 + i.val) / 65536 = 13 := by omega
    have quotient : ((851968 + i.val) % 65536) / 8192 = 0 := by omega
    rw [srlLowOutput,shift]
    norm_num only
    rw [quotient]
    simpa using affine_get 8192 0 0 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (860160 + i.val) / 65536 = 13 := by omega
    have quotient : ((860160 + i.val) % 65536) / 8192 = 1 := by omega
    rw [srlLowOutput,shift]
    norm_num only
    rw [quotient]
    simpa using affine_get 8192 1 0 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (868352 + i.val) / 65536 = 13 := by omega
    have quotient : ((868352 + i.val) % 65536) / 8192 = 2 := by omega
    rw [srlLowOutput,shift]
    norm_num only
    rw [quotient]
    simpa using affine_get 8192 2 0 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (876544 + i.val) / 65536 = 13 := by omega
    have quotient : ((876544 + i.val) % 65536) / 8192 = 3 := by omega
    rw [srlLowOutput,shift]
    norm_num only
    rw [quotient]
    simpa using affine_get 8192 3 0 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (884736 + i.val) / 65536 = 13 := by omega
    have quotient : ((884736 + i.val) % 65536) / 8192 = 4 := by omega
    rw [srlLowOutput,shift]
    norm_num only
    rw [quotient]
    simpa using affine_get 8192 4 0 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (892928 + i.val) / 65536 = 13 := by omega
    have quotient : ((892928 + i.val) % 65536) / 8192 = 5 := by omega
    rw [srlLowOutput,shift]
    norm_num only
    rw [quotient]
    simpa using affine_get 8192 5 0 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (901120 + i.val) / 65536 = 13 := by omega
    have quotient : ((901120 + i.val) % 65536) / 8192 = 6 := by omega
    rw [srlLowOutput,shift]
    norm_num only
    rw [quotient]
    simpa using affine_get 8192 6 0 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (909312 + i.val) / 65536 = 13 := by omega
    have quotient : ((909312 + i.val) % 65536) / 8192 = 7 := by omega
    rw [srlLowOutput,shift]
    norm_num only
    rw [quotient]
    simpa using affine_get 8192 7 0 i.val inside

end Airbender.Verification.SrlLowProofs
