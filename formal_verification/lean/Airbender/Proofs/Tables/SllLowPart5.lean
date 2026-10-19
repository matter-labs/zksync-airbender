import Airbender.Proofs.Tables.SllLowParts

namespace Airbender.Verification.SllLowProofs
open Setup Setup.Proofs NativeSllLow
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

theorem outputs_part5 : checkBlocks sllLowHighOutput 393216 part5 = true := by
  rw [part5_shape]
  simp only [checkBlocks_cons_iff,checkBlocks_nil,and_true,Block.length,
    Array.size_replicate,Nat.reduceMul,Nat.reduceAdd]
  repeat' apply And.intro
  · intro i
    have inside : i.val < 65536 := by simpa only [Block.length,Array.size_replicate] using i.isLt
    have sh : (393216 + i.val) / 65536 = 6 := by omega
    have value : (((393216 + i.val) % 65536) * 64 / 65536) % 65536 = i.val / 1024 := by omega
    rw [sllLowHighOutput,sh]
    norm_num only
    rw [value]
    simpa only [Nat.cast_one,Array.getElem_replicate,Array.size_replicate,Nat.zero_add,Nat.one_mul] using
      periodic_get (Array.replicate 1024 0) 64 1 i.val (by simp)
        (by simpa only [Array.size_replicate,Nat.reduceMul] using inside)
  · intro i
    have inside : i.val < 65536 := by simpa only [Block.length,Array.size_replicate] using i.isLt
    have sh : (458752 + i.val) / 65536 = 7 := by omega
    have value : (((458752 + i.val) % 65536) * 128 / 65536) % 65536 = i.val / 512 := by omega
    rw [sllLowHighOutput,sh]
    norm_num only
    rw [value]
    simpa only [Nat.cast_one,Array.getElem_replicate,Array.size_replicate,Nat.zero_add,Nat.one_mul] using
      periodic_get (Array.replicate 512 0) 128 1 i.val (by simp)
        (by simpa only [Array.size_replicate,Nat.reduceMul] using inside)
  · intro i
    have inside : i.val < 65536 := by simpa only [Block.length,Array.size_replicate] using i.isLt
    have sh : (524288 + i.val) / 65536 = 8 := by omega
    have value : (((524288 + i.val) % 65536) * 256 / 65536) % 65536 = i.val / 256 := by omega
    rw [sllLowHighOutput,sh]
    norm_num only
    rw [value]
    simpa only [Nat.cast_one,Array.getElem_replicate,Array.size_replicate,Nat.zero_add,Nat.one_mul] using
      periodic_get (Array.replicate 256 0) 256 1 i.val (by simp)
        (by simpa only [Array.size_replicate,Nat.reduceMul] using inside)
  · intro i
    have inside : i.val < 65536 := by simpa only [Block.length,Array.size_replicate] using i.isLt
    have sh : (589824 + i.val) / 65536 = 9 := by omega
    have value : (((589824 + i.val) % 65536) * 512 / 65536) % 65536 = i.val / 128 := by omega
    rw [sllLowHighOutput,sh]
    norm_num only
    rw [value]
    simpa only [Nat.cast_one,Array.getElem_replicate,Array.size_replicate,Nat.zero_add,Nat.one_mul] using
      periodic_get (Array.replicate 128 0) 512 1 i.val (by simp)
        (by simpa only [Array.size_replicate,Nat.reduceMul] using inside)
  · intro i
    have inside : i.val < 65536 := by simpa only [Block.length,Array.size_replicate] using i.isLt
    have sh : (655360 + i.val) / 65536 = 10 := by omega
    have value : (((655360 + i.val) % 65536) * 1024 / 65536) % 65536 = i.val / 64 := by omega
    rw [sllLowHighOutput,sh]
    norm_num only
    rw [value]
    simpa only [Nat.cast_one,Array.getElem_replicate,Array.size_replicate,Nat.zero_add,Nat.one_mul] using
      periodic_get (Array.replicate 64 0) 1024 1 i.val (by simp)
        (by simpa only [Array.size_replicate,Nat.reduceMul] using inside)
  · intro i
    have inside : i.val < 65536 := by simpa only [Block.length,Array.size_replicate] using i.isLt
    have sh : (720896 + i.val) / 65536 = 11 := by omega
    have value : (((720896 + i.val) % 65536) * 2048 / 65536) % 65536 = i.val / 32 := by omega
    rw [sllLowHighOutput,sh]
    norm_num only
    rw [value]
    simpa only [Nat.cast_one,Array.getElem_replicate,Array.size_replicate,Nat.zero_add,Nat.one_mul] using
      periodic_get (Array.replicate 32 0) 2048 1 i.val (by simp)
        (by simpa only [Array.size_replicate,Nat.reduceMul] using inside)
  · intro i
    have inside : i.val < 65536 := by simpa only [Block.length,Array.size_replicate] using i.isLt
    have sh : (786432 + i.val) / 65536 = 12 := by omega
    have value : (((786432 + i.val) % 65536) * 4096 / 65536) % 65536 = i.val / 16 := by omega
    rw [sllLowHighOutput,sh]
    norm_num only
    rw [value]
    simpa only [Nat.cast_one,Array.getElem_replicate,Array.size_replicate,Nat.zero_add,Nat.one_mul] using
      periodic_get (Array.replicate 16 0) 4096 1 i.val (by simp)
        (by simpa only [Array.size_replicate,Nat.reduceMul] using inside)
  · intro i
    have inside : i.val < 65536 := by simpa only [Block.length,Array.size_replicate] using i.isLt
    have sh : (851968 + i.val) / 65536 = 13 := by omega
    have value : (((851968 + i.val) % 65536) * 8192 / 65536) % 65536 = i.val / 8 := by omega
    rw [sllLowHighOutput,sh]
    norm_num only
    rw [value]
    simpa only [Nat.cast_one,Array.getElem_replicate,Array.size_replicate,Nat.zero_add,Nat.one_mul] using
      periodic_get (Array.replicate 8 0) 8192 1 i.val (by simp)
        (by simpa only [Array.size_replicate,Nat.reduceMul] using inside)
  · intro i
    have inside : i.val < 65536 := by simpa only [Block.length,Array.size_replicate] using i.isLt
    have sh : (917504 + i.val) / 65536 = 14 := by omega
    have value : (((917504 + i.val) % 65536) * 16384 / 65536) % 65536 = i.val / 4 := by omega
    rw [sllLowHighOutput,sh]
    norm_num only
    rw [value]
    simpa only [Nat.cast_one,Array.getElem_replicate,Array.size_replicate,Nat.zero_add,Nat.one_mul] using
      periodic_get (Array.replicate 4 0) 16384 1 i.val (by simp)
        (by simpa only [Array.size_replicate,Nat.reduceMul] using inside)
  · intro i
    have inside : i.val < 65536 := by simpa only [Block.length,Array.size_replicate] using i.isLt
    have sh : (983040 + i.val) / 65536 = 15 := by omega
    have value : (((983040 + i.val) % 65536) * 32768 / 65536) % 65536 = i.val / 2 := by omega
    rw [sllLowHighOutput,sh]
    norm_num only
    rw [value]
    simpa only [Nat.cast_one,Array.getElem_replicate,Array.size_replicate,Nat.zero_add,Nat.one_mul] using
      periodic_get (Array.replicate 2 0) 32768 1 i.val (by simp)
        (by simpa only [Array.size_replicate,Nat.reduceMul] using inside)

end Airbender.Verification.SllLowProofs
