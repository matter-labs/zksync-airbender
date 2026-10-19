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

theorem outputs_part2 : checkBlocks srlLowOutput 786432 part2 = true := by
  rw [part2_shape]
  simp only [checkBlocks_cons_iff,checkBlocks_nil,and_true,Block.length,
    Nat.reduceAdd]
  repeat' apply And.intro
  · intro i
    have inside := i.isLt
    have shift : (786432 + i.val) / 65536 = 12 := by omega
    have quotient : ((786432 + i.val) % 65536) / 4096 = 0 := by omega
    rw [srlLowOutput,shift]
    norm_num only
    rw [quotient]
    simpa using affine_get 4096 0 0 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (790528 + i.val) / 65536 = 12 := by omega
    have quotient : ((790528 + i.val) % 65536) / 4096 = 1 := by omega
    rw [srlLowOutput,shift]
    norm_num only
    rw [quotient]
    simpa using affine_get 4096 1 0 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (794624 + i.val) / 65536 = 12 := by omega
    have quotient : ((794624 + i.val) % 65536) / 4096 = 2 := by omega
    rw [srlLowOutput,shift]
    norm_num only
    rw [quotient]
    simpa using affine_get 4096 2 0 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (798720 + i.val) / 65536 = 12 := by omega
    have quotient : ((798720 + i.val) % 65536) / 4096 = 3 := by omega
    rw [srlLowOutput,shift]
    norm_num only
    rw [quotient]
    simpa using affine_get 4096 3 0 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (802816 + i.val) / 65536 = 12 := by omega
    have quotient : ((802816 + i.val) % 65536) / 4096 = 4 := by omega
    rw [srlLowOutput,shift]
    norm_num only
    rw [quotient]
    simpa using affine_get 4096 4 0 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (806912 + i.val) / 65536 = 12 := by omega
    have quotient : ((806912 + i.val) % 65536) / 4096 = 5 := by omega
    rw [srlLowOutput,shift]
    norm_num only
    rw [quotient]
    simpa using affine_get 4096 5 0 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (811008 + i.val) / 65536 = 12 := by omega
    have quotient : ((811008 + i.val) % 65536) / 4096 = 6 := by omega
    rw [srlLowOutput,shift]
    norm_num only
    rw [quotient]
    simpa using affine_get 4096 6 0 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (815104 + i.val) / 65536 = 12 := by omega
    have quotient : ((815104 + i.val) % 65536) / 4096 = 7 := by omega
    rw [srlLowOutput,shift]
    norm_num only
    rw [quotient]
    simpa using affine_get 4096 7 0 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (819200 + i.val) / 65536 = 12 := by omega
    have quotient : ((819200 + i.val) % 65536) / 4096 = 8 := by omega
    rw [srlLowOutput,shift]
    norm_num only
    rw [quotient]
    simpa using affine_get 4096 8 0 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (823296 + i.val) / 65536 = 12 := by omega
    have quotient : ((823296 + i.val) % 65536) / 4096 = 9 := by omega
    rw [srlLowOutput,shift]
    norm_num only
    rw [quotient]
    simpa using affine_get 4096 9 0 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (827392 + i.val) / 65536 = 12 := by omega
    have quotient : ((827392 + i.val) % 65536) / 4096 = 10 := by omega
    rw [srlLowOutput,shift]
    norm_num only
    rw [quotient]
    simpa using affine_get 4096 10 0 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (831488 + i.val) / 65536 = 12 := by omega
    have quotient : ((831488 + i.val) % 65536) / 4096 = 11 := by omega
    rw [srlLowOutput,shift]
    norm_num only
    rw [quotient]
    simpa using affine_get 4096 11 0 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (835584 + i.val) / 65536 = 12 := by omega
    have quotient : ((835584 + i.val) % 65536) / 4096 = 12 := by omega
    rw [srlLowOutput,shift]
    norm_num only
    rw [quotient]
    simpa using affine_get 4096 12 0 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (839680 + i.val) / 65536 = 12 := by omega
    have quotient : ((839680 + i.val) % 65536) / 4096 = 13 := by omega
    rw [srlLowOutput,shift]
    norm_num only
    rw [quotient]
    simpa using affine_get 4096 13 0 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (843776 + i.val) / 65536 = 12 := by omega
    have quotient : ((843776 + i.val) % 65536) / 4096 = 14 := by omega
    rw [srlLowOutput,shift]
    norm_num only
    rw [quotient]
    simpa using affine_get 4096 14 0 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (847872 + i.val) / 65536 = 12 := by omega
    have quotient : ((847872 + i.val) % 65536) / 4096 = 15 := by omega
    rw [srlLowOutput,shift]
    norm_num only
    rw [quotient]
    simpa using affine_get 4096 15 0 i.val inside

end Airbender.Verification.SrlLowProofs
