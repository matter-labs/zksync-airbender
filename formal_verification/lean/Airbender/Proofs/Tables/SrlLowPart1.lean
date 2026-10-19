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

theorem outputs_part1 : checkBlocks srlLowOutput 720896 part1 = true := by
  rw [part1_shape]
  simp only [checkBlocks_cons_iff,checkBlocks_nil,and_true,Block.length,
    Nat.reduceAdd]
  repeat' apply And.intro
  · intro i
    have inside := i.isLt
    have shift : (720896 + i.val) / 65536 = 11 := by omega
    have quotient : ((720896 + i.val) % 65536) / 2048 = 0 := by omega
    rw [srlLowOutput,shift]
    norm_num only
    rw [quotient]
    simpa using affine_get 2048 0 0 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (722944 + i.val) / 65536 = 11 := by omega
    have quotient : ((722944 + i.val) % 65536) / 2048 = 1 := by omega
    rw [srlLowOutput,shift]
    norm_num only
    rw [quotient]
    simpa using affine_get 2048 1 0 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (724992 + i.val) / 65536 = 11 := by omega
    have quotient : ((724992 + i.val) % 65536) / 2048 = 2 := by omega
    rw [srlLowOutput,shift]
    norm_num only
    rw [quotient]
    simpa using affine_get 2048 2 0 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (727040 + i.val) / 65536 = 11 := by omega
    have quotient : ((727040 + i.val) % 65536) / 2048 = 3 := by omega
    rw [srlLowOutput,shift]
    norm_num only
    rw [quotient]
    simpa using affine_get 2048 3 0 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (729088 + i.val) / 65536 = 11 := by omega
    have quotient : ((729088 + i.val) % 65536) / 2048 = 4 := by omega
    rw [srlLowOutput,shift]
    norm_num only
    rw [quotient]
    simpa using affine_get 2048 4 0 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (731136 + i.val) / 65536 = 11 := by omega
    have quotient : ((731136 + i.val) % 65536) / 2048 = 5 := by omega
    rw [srlLowOutput,shift]
    norm_num only
    rw [quotient]
    simpa using affine_get 2048 5 0 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (733184 + i.val) / 65536 = 11 := by omega
    have quotient : ((733184 + i.val) % 65536) / 2048 = 6 := by omega
    rw [srlLowOutput,shift]
    norm_num only
    rw [quotient]
    simpa using affine_get 2048 6 0 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (735232 + i.val) / 65536 = 11 := by omega
    have quotient : ((735232 + i.val) % 65536) / 2048 = 7 := by omega
    rw [srlLowOutput,shift]
    norm_num only
    rw [quotient]
    simpa using affine_get 2048 7 0 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (737280 + i.val) / 65536 = 11 := by omega
    have quotient : ((737280 + i.val) % 65536) / 2048 = 8 := by omega
    rw [srlLowOutput,shift]
    norm_num only
    rw [quotient]
    simpa using affine_get 2048 8 0 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (739328 + i.val) / 65536 = 11 := by omega
    have quotient : ((739328 + i.val) % 65536) / 2048 = 9 := by omega
    rw [srlLowOutput,shift]
    norm_num only
    rw [quotient]
    simpa using affine_get 2048 9 0 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (741376 + i.val) / 65536 = 11 := by omega
    have quotient : ((741376 + i.val) % 65536) / 2048 = 10 := by omega
    rw [srlLowOutput,shift]
    norm_num only
    rw [quotient]
    simpa using affine_get 2048 10 0 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (743424 + i.val) / 65536 = 11 := by omega
    have quotient : ((743424 + i.val) % 65536) / 2048 = 11 := by omega
    rw [srlLowOutput,shift]
    norm_num only
    rw [quotient]
    simpa using affine_get 2048 11 0 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (745472 + i.val) / 65536 = 11 := by omega
    have quotient : ((745472 + i.val) % 65536) / 2048 = 12 := by omega
    rw [srlLowOutput,shift]
    norm_num only
    rw [quotient]
    simpa using affine_get 2048 12 0 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (747520 + i.val) / 65536 = 11 := by omega
    have quotient : ((747520 + i.val) % 65536) / 2048 = 13 := by omega
    rw [srlLowOutput,shift]
    norm_num only
    rw [quotient]
    simpa using affine_get 2048 13 0 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (749568 + i.val) / 65536 = 11 := by omega
    have quotient : ((749568 + i.val) % 65536) / 2048 = 14 := by omega
    rw [srlLowOutput,shift]
    norm_num only
    rw [quotient]
    simpa using affine_get 2048 14 0 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (751616 + i.val) / 65536 = 11 := by omega
    have quotient : ((751616 + i.val) % 65536) / 2048 = 15 := by omega
    rw [srlLowOutput,shift]
    norm_num only
    rw [quotient]
    simpa using affine_get 2048 15 0 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (753664 + i.val) / 65536 = 11 := by omega
    have quotient : ((753664 + i.val) % 65536) / 2048 = 16 := by omega
    rw [srlLowOutput,shift]
    norm_num only
    rw [quotient]
    simpa using affine_get 2048 16 0 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (755712 + i.val) / 65536 = 11 := by omega
    have quotient : ((755712 + i.val) % 65536) / 2048 = 17 := by omega
    rw [srlLowOutput,shift]
    norm_num only
    rw [quotient]
    simpa using affine_get 2048 17 0 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (757760 + i.val) / 65536 = 11 := by omega
    have quotient : ((757760 + i.val) % 65536) / 2048 = 18 := by omega
    rw [srlLowOutput,shift]
    norm_num only
    rw [quotient]
    simpa using affine_get 2048 18 0 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (759808 + i.val) / 65536 = 11 := by omega
    have quotient : ((759808 + i.val) % 65536) / 2048 = 19 := by omega
    rw [srlLowOutput,shift]
    norm_num only
    rw [quotient]
    simpa using affine_get 2048 19 0 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (761856 + i.val) / 65536 = 11 := by omega
    have quotient : ((761856 + i.val) % 65536) / 2048 = 20 := by omega
    rw [srlLowOutput,shift]
    norm_num only
    rw [quotient]
    simpa using affine_get 2048 20 0 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (763904 + i.val) / 65536 = 11 := by omega
    have quotient : ((763904 + i.val) % 65536) / 2048 = 21 := by omega
    rw [srlLowOutput,shift]
    norm_num only
    rw [quotient]
    simpa using affine_get 2048 21 0 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (765952 + i.val) / 65536 = 11 := by omega
    have quotient : ((765952 + i.val) % 65536) / 2048 = 22 := by omega
    rw [srlLowOutput,shift]
    norm_num only
    rw [quotient]
    simpa using affine_get 2048 22 0 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (768000 + i.val) / 65536 = 11 := by omega
    have quotient : ((768000 + i.val) % 65536) / 2048 = 23 := by omega
    rw [srlLowOutput,shift]
    norm_num only
    rw [quotient]
    simpa using affine_get 2048 23 0 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (770048 + i.val) / 65536 = 11 := by omega
    have quotient : ((770048 + i.val) % 65536) / 2048 = 24 := by omega
    rw [srlLowOutput,shift]
    norm_num only
    rw [quotient]
    simpa using affine_get 2048 24 0 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (772096 + i.val) / 65536 = 11 := by omega
    have quotient : ((772096 + i.val) % 65536) / 2048 = 25 := by omega
    rw [srlLowOutput,shift]
    norm_num only
    rw [quotient]
    simpa using affine_get 2048 25 0 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (774144 + i.val) / 65536 = 11 := by omega
    have quotient : ((774144 + i.val) % 65536) / 2048 = 26 := by omega
    rw [srlLowOutput,shift]
    norm_num only
    rw [quotient]
    simpa using affine_get 2048 26 0 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (776192 + i.val) / 65536 = 11 := by omega
    have quotient : ((776192 + i.val) % 65536) / 2048 = 27 := by omega
    rw [srlLowOutput,shift]
    norm_num only
    rw [quotient]
    simpa using affine_get 2048 27 0 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (778240 + i.val) / 65536 = 11 := by omega
    have quotient : ((778240 + i.val) % 65536) / 2048 = 28 := by omega
    rw [srlLowOutput,shift]
    norm_num only
    rw [quotient]
    simpa using affine_get 2048 28 0 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (780288 + i.val) / 65536 = 11 := by omega
    have quotient : ((780288 + i.val) % 65536) / 2048 = 29 := by omega
    rw [srlLowOutput,shift]
    norm_num only
    rw [quotient]
    simpa using affine_get 2048 29 0 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (782336 + i.val) / 65536 = 11 := by omega
    have quotient : ((782336 + i.val) % 65536) / 2048 = 30 := by omega
    rw [srlLowOutput,shift]
    norm_num only
    rw [quotient]
    simpa using affine_get 2048 30 0 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (784384 + i.val) / 65536 = 11 := by omega
    have quotient : ((784384 + i.val) % 65536) / 2048 = 31 := by omega
    rw [srlLowOutput,shift]
    norm_num only
    rw [quotient]
    simpa using affine_get 2048 31 0 i.val inside

end Airbender.Verification.SrlLowProofs
