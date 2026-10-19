import Airbender.Proofs.Tables.SllHighParts

namespace Airbender.Verification.SllHighProofs
open Setup Setup.Proofs NativeSllHigh
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

private theorem periodic_stored_get (values : Array Nat) (size count step n : Nat)
    (size_eq : values.size = size) (positive : 0 < size) (bound : n < count * size)
    (stored : ∀ i : Fin size, values[i.val]? = some (i.val * step)) :
    Block.get? (.periodic count 0 values) n = some ((n % size) * step) := by
  have inside : n % size < values.size := by rw [size_eq]; exact Nat.mod_lt _ positive
  have selected : values[n % size] = (n % size) * step := by
    have result := stored ⟨n % size,Nat.mod_lt _ positive⟩
    simpa only [Array.getElem?_eq_getElem inside,Option.some.injEq] using result
  simpa only [size_eq,selected,Nat.cast_zero,Nat.zero_mul,Nat.add_zero] using
    periodic_get values count 0 n (by rw [size_eq]; exact positive) (by rw [size_eq]; exact bound)


private theorem periodic_partition (a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : Array Nat)
    (size6 : a6.size = 1024)
    (size7 : a7.size = 512)
    (size8 : a8.size = 256)
    (size9 : a9.size = 128)
    (size10 : a10.size = 64)
    (size11 : a11.size = 32)
    (size12 : a12.size = 16)
    (size13 : a13.size = 8)
    (size14 : a14.size = 4)
    (size15 : a15.size = 2)
    (stored6 : ∀ j : Fin 1024, a6[j.val]? = some (j.val * 64))
    (stored7 : ∀ j : Fin 512, a7[j.val]? = some (j.val * 128))
    (stored8 : ∀ j : Fin 256, a8[j.val]? = some (j.val * 256))
    (stored9 : ∀ j : Fin 128, a9[j.val]? = some (j.val * 512))
    (stored10 : ∀ j : Fin 64, a10[j.val]? = some (j.val * 1024))
    (stored11 : ∀ j : Fin 32, a11[j.val]? = some (j.val * 2048))
    (stored12 : ∀ j : Fin 16, a12[j.val]? = some (j.val * 4096))
    (stored13 : ∀ j : Fin 8, a13[j.val]? = some (j.val * 8192))
    (stored14 : ∀ j : Fin 4, a14[j.val]? = some (j.val * 16384))
    (stored15 : ∀ j : Fin 2, a15[j.val]? = some (j.val * 32768))
    : checkBlocks sllHighOutput 393216 [.periodic 64 0 a6, .periodic 128 0 a7, .periodic 256 0 a8, .periodic 512 0 a9, .periodic 1024 0 a10, .periodic 2048 0 a11, .periodic 4096 0 a12, .periodic 8192 0 a13, .periodic 16384 0 a14, .periodic 32768 0 a15] = true := by
  simp only [checkBlocks_cons_iff,checkBlocks_nil,and_true,Block.length,
    size6,size7,size8,size9,size10,size11,size12,size13,size14,size15,Nat.reduceMul,Nat.reduceAdd]
  repeat' apply And.intro
  · intro i
    have inside : i.val < 65536 := by simpa only [Block.length,size6] using i.isLt
    have shift : (393216 + i.val) / 65536 = 6 := by omega
    have result : (((393216 + i.val) % 65536) * 64) % 65536 = (i.val % 1024) * 64 := by omega
    rw [sllHighOutput,shift]
    norm_num only
    rw [result]
    exact periodic_stored_get a6 1024 64 64 i.val size6 (by decide) (by simpa only [Block.length,size6] using i.isLt) stored6
  · intro i
    have inside : i.val < 65536 := by simpa only [Block.length,size7] using i.isLt
    have shift : (458752 + i.val) / 65536 = 7 := by omega
    have result : (((458752 + i.val) % 65536) * 128) % 65536 = (i.val % 512) * 128 := by omega
    rw [sllHighOutput,shift]
    norm_num only
    rw [result]
    exact periodic_stored_get a7 512 128 128 i.val size7 (by decide) (by simpa only [Block.length,size7] using i.isLt) stored7
  · intro i
    have inside : i.val < 65536 := by simpa only [Block.length,size8] using i.isLt
    have shift : (524288 + i.val) / 65536 = 8 := by omega
    have result : (((524288 + i.val) % 65536) * 256) % 65536 = (i.val % 256) * 256 := by omega
    rw [sllHighOutput,shift]
    norm_num only
    rw [result]
    exact periodic_stored_get a8 256 256 256 i.val size8 (by decide) (by simpa only [Block.length,size8] using i.isLt) stored8
  · intro i
    have inside : i.val < 65536 := by simpa only [Block.length,size9] using i.isLt
    have shift : (589824 + i.val) / 65536 = 9 := by omega
    have result : (((589824 + i.val) % 65536) * 512) % 65536 = (i.val % 128) * 512 := by omega
    rw [sllHighOutput,shift]
    norm_num only
    rw [result]
    exact periodic_stored_get a9 128 512 512 i.val size9 (by decide) (by simpa only [Block.length,size9] using i.isLt) stored9
  · intro i
    have inside : i.val < 65536 := by simpa only [Block.length,size10] using i.isLt
    have shift : (655360 + i.val) / 65536 = 10 := by omega
    have result : (((655360 + i.val) % 65536) * 1024) % 65536 = (i.val % 64) * 1024 := by omega
    rw [sllHighOutput,shift]
    norm_num only
    rw [result]
    exact periodic_stored_get a10 64 1024 1024 i.val size10 (by decide) (by simpa only [Block.length,size10] using i.isLt) stored10
  · intro i
    have inside : i.val < 65536 := by simpa only [Block.length,size11] using i.isLt
    have shift : (720896 + i.val) / 65536 = 11 := by omega
    have result : (((720896 + i.val) % 65536) * 2048) % 65536 = (i.val % 32) * 2048 := by omega
    rw [sllHighOutput,shift]
    norm_num only
    rw [result]
    exact periodic_stored_get a11 32 2048 2048 i.val size11 (by decide) (by simpa only [Block.length,size11] using i.isLt) stored11
  · intro i
    have inside : i.val < 65536 := by simpa only [Block.length,size12] using i.isLt
    have shift : (786432 + i.val) / 65536 = 12 := by omega
    have result : (((786432 + i.val) % 65536) * 4096) % 65536 = (i.val % 16) * 4096 := by omega
    rw [sllHighOutput,shift]
    norm_num only
    rw [result]
    exact periodic_stored_get a12 16 4096 4096 i.val size12 (by decide) (by simpa only [Block.length,size12] using i.isLt) stored12
  · intro i
    have inside : i.val < 65536 := by simpa only [Block.length,size13] using i.isLt
    have shift : (851968 + i.val) / 65536 = 13 := by omega
    have result : (((851968 + i.val) % 65536) * 8192) % 65536 = (i.val % 8) * 8192 := by omega
    rw [sllHighOutput,shift]
    norm_num only
    rw [result]
    exact periodic_stored_get a13 8 8192 8192 i.val size13 (by decide) (by simpa only [Block.length,size13] using i.isLt) stored13
  · intro i
    have inside : i.val < 65536 := by simpa only [Block.length,size14] using i.isLt
    have shift : (917504 + i.val) / 65536 = 14 := by omega
    have result : (((917504 + i.val) % 65536) * 16384) % 65536 = (i.val % 4) * 16384 := by omega
    rw [sllHighOutput,shift]
    norm_num only
    rw [result]
    exact periodic_stored_get a14 4 16384 16384 i.val size14 (by decide) (by simpa only [Block.length,size14] using i.isLt) stored14
  · intro i
    have inside : i.val < 65536 := by simpa only [Block.length,size15] using i.isLt
    have shift : (983040 + i.val) / 65536 = 15 := by omega
    have result : (((983040 + i.val) % 65536) * 32768) % 65536 = (i.val % 2) * 32768 := by omega
    rw [sllHighOutput,shift]
    norm_num only
    rw [result]
    exact periodic_stored_get a15 2 32768 32768 i.val size15 (by decide) (by simpa only [Block.length,size15] using i.isLt) stored15


theorem outputs_part4 : checkBlocks sllHighOutput 393216 part4 = true := by
  exact Eq.mpr (congrArg (fun blocks : List Block => checkBlocks sllHighOutput 393216 blocks = true)
      part4_shape)
    (periodic_partition template6 template7 template8 template9 template10 template11 template12 template13 template14 template15
      template6_size template7_size template8_size template9_size template10_size template11_size template12_size template13_size template14_size template15_size
      template6_values template7_values template8_values template9_values template10_values template11_values template12_values template13_values template14_values template15_values)

end Airbender.Verification.SllHighProofs
