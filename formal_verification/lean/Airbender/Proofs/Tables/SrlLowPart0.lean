import Airbender.Proofs.Tables.SrlLowParts

namespace Airbender.Verification.SrlLowProofs
open Setup Setup.Proofs NativeSrlLow
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

private theorem affine_get (length first step n : Nat) (bound : n < length) :
    Block.get? (.affine length first (step : Int)) n = some (first + step * n) := by
  simp only [Block.get?, Block.length, if_pos bound]
  have casts : (first : Int) + (step : Int) * n = ((first + step * n : Nat) : Int) := by simp
  rw [casts, if_pos (Int.natCast_nonneg _), Int.toNat_natCast]

theorem outputs_part0 : checkBlocks srlLowOutput 0 part0 = true := by
  rw [part0_shape]
  simp only [checkBlocks_cons_iff,checkBlocks_nil,and_true,Block.length,
    Array.size_replicate,Nat.reduceMul,Nat.reduceAdd]
  repeat' apply And.intro
  · intro i
    have inside : i.val < 65536 := by simpa only [Block.length,Array.size_replicate] using i.isLt
    have shift : (0 + i.val) / 65536 = 0 := by omega
    have remainder : (0 + i.val) % 65536 = i.val := by omega
    rw [srlLowOutput,shift,remainder]
    simpa using affine_get 65536 0 1 i.val inside
  · intro i
    have inside : i.val < 65536 := by simpa only [Block.length,Array.size_replicate] using i.isLt
    have shift : (65536 + i.val) / 65536 = 1 := by omega
    have remainder : (65536 + i.val) % 65536 = i.val := by omega
    rw [srlLowOutput,shift,remainder]
    simpa only [Nat.cast_one,Array.getElem_replicate,Array.size_replicate,Nat.zero_add,Nat.one_mul,Nat.reducePow] using periodic_get (Array.replicate 2 0) 32768 1 i.val (by simp) (by simpa only [Array.size_replicate,Nat.reduceMul] using inside)
  · intro i
    have inside : i.val < 65536 := by simpa only [Block.length,Array.size_replicate] using i.isLt
    have shift : (131072 + i.val) / 65536 = 2 := by omega
    have remainder : (131072 + i.val) % 65536 = i.val := by omega
    rw [srlLowOutput,shift,remainder]
    simpa only [Nat.cast_one,Array.getElem_replicate,Array.size_replicate,Nat.zero_add,Nat.one_mul,Nat.reducePow] using periodic_get (Array.replicate 4 0) 16384 1 i.val (by simp) (by simpa only [Array.size_replicate,Nat.reduceMul] using inside)
  · intro i
    have inside : i.val < 65536 := by simpa only [Block.length,Array.size_replicate] using i.isLt
    have shift : (196608 + i.val) / 65536 = 3 := by omega
    have remainder : (196608 + i.val) % 65536 = i.val := by omega
    rw [srlLowOutput,shift,remainder]
    simpa only [Nat.cast_one,Array.getElem_replicate,Array.size_replicate,Nat.zero_add,Nat.one_mul,Nat.reducePow] using periodic_get (Array.replicate 8 0) 8192 1 i.val (by simp) (by simpa only [Array.size_replicate,Nat.reduceMul] using inside)
  · intro i
    have inside : i.val < 65536 := by simpa only [Block.length,Array.size_replicate] using i.isLt
    have shift : (262144 + i.val) / 65536 = 4 := by omega
    have remainder : (262144 + i.val) % 65536 = i.val := by omega
    rw [srlLowOutput,shift,remainder]
    simpa only [Nat.cast_one,Array.getElem_replicate,Array.size_replicate,Nat.zero_add,Nat.one_mul,Nat.reducePow] using periodic_get (Array.replicate 16 0) 4096 1 i.val (by simp) (by simpa only [Array.size_replicate,Nat.reduceMul] using inside)
  · intro i
    have inside : i.val < 65536 := by simpa only [Block.length,Array.size_replicate] using i.isLt
    have shift : (327680 + i.val) / 65536 = 5 := by omega
    have remainder : (327680 + i.val) % 65536 = i.val := by omega
    rw [srlLowOutput,shift,remainder]
    simpa only [Nat.cast_one,Array.getElem_replicate,Array.size_replicate,Nat.zero_add,Nat.one_mul,Nat.reducePow] using periodic_get (Array.replicate 32 0) 2048 1 i.val (by simp) (by simpa only [Array.size_replicate,Nat.reduceMul] using inside)
  · intro i
    have inside : i.val < 65536 := by simpa only [Block.length,Array.size_replicate] using i.isLt
    have shift : (393216 + i.val) / 65536 = 6 := by omega
    have remainder : (393216 + i.val) % 65536 = i.val := by omega
    rw [srlLowOutput,shift,remainder]
    simpa only [Nat.cast_one,Array.getElem_replicate,Array.size_replicate,Nat.zero_add,Nat.one_mul,Nat.reducePow] using periodic_get (Array.replicate 64 0) 1024 1 i.val (by simp) (by simpa only [Array.size_replicate,Nat.reduceMul] using inside)
  · intro i
    have inside : i.val < 65536 := by simpa only [Block.length,Array.size_replicate] using i.isLt
    have shift : (458752 + i.val) / 65536 = 7 := by omega
    have remainder : (458752 + i.val) % 65536 = i.val := by omega
    rw [srlLowOutput,shift,remainder]
    simpa only [Nat.cast_one,Array.getElem_replicate,Array.size_replicate,Nat.zero_add,Nat.one_mul,Nat.reducePow] using periodic_get (Array.replicate 128 0) 512 1 i.val (by simp) (by simpa only [Array.size_replicate,Nat.reduceMul] using inside)
  · intro i
    have inside : i.val < 65536 := by simpa only [Block.length,Array.size_replicate] using i.isLt
    have shift : (524288 + i.val) / 65536 = 8 := by omega
    have remainder : (524288 + i.val) % 65536 = i.val := by omega
    rw [srlLowOutput,shift,remainder]
    simpa only [Nat.cast_one,Array.getElem_replicate,Array.size_replicate,Nat.zero_add,Nat.one_mul,Nat.reducePow] using periodic_get (Array.replicate 256 0) 256 1 i.val (by simp) (by simpa only [Array.size_replicate,Nat.reduceMul] using inside)
  · intro i
    have inside : i.val < 65536 := by simpa only [Block.length,Array.size_replicate] using i.isLt
    have shift : (589824 + i.val) / 65536 = 9 := by omega
    have remainder : (589824 + i.val) % 65536 = i.val := by omega
    rw [srlLowOutput,shift,remainder]
    simpa only [Nat.cast_one,Array.getElem_replicate,Array.size_replicate,Nat.zero_add,Nat.one_mul,Nat.reducePow] using periodic_get (Array.replicate 512 0) 128 1 i.val (by simp) (by simpa only [Array.size_replicate,Nat.reduceMul] using inside)
  · intro i
    have inside : i.val < 65536 := by simpa only [Block.length,Array.size_replicate] using i.isLt
    have shift : (655360 + i.val) / 65536 = 10 := by omega
    have remainder : (655360 + i.val) % 65536 = i.val := by omega
    rw [srlLowOutput,shift,remainder]
    simpa only [Nat.cast_one,Array.getElem_replicate,Array.size_replicate,Nat.zero_add,Nat.one_mul,Nat.reducePow] using periodic_get (Array.replicate 1024 0) 64 1 i.val (by simp) (by simpa only [Array.size_replicate,Nat.reduceMul] using inside)

end Airbender.Verification.SrlLowProofs
