import Airbender.Proofs.Tables.SrlHighParts

namespace Airbender.Verification.SrlHighProofs
open Setup Setup.Proofs NativeSrlHigh
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

private theorem affine_get (length first step n : Nat) (bound : n < length) :
    Block.get? (.affine length first (step : Int)) n = some (first + step * n) := by
  simp only [Block.get?, Block.length, if_pos bound]
  have casts : (first : Int) + (step : Int) * n = ((first + step * n : Nat) : Int) := by simp
  rw [casts, if_pos (Int.natCast_nonneg _), Int.toNat_natCast]

private theorem periodic_stored_get (values : Array Nat) (size count step n : Nat)
    (size_eq : values.size = size) (positive : 0 < size) (bound : n < count * size)
    (stored : ∀ i : Fin size, values[i.val]? = some (((i.val + 1) % size) * step)) :
    Block.get? (.periodic count 0 values) n = some ((((n % size) + 1) % size) * step) := by
  have inside : n % size < values.size := by rw [size_eq]; exact Nat.mod_lt _ positive
  have selected : values[n % size] = (((n % size) + 1) % size) * step := by
    have result := stored ⟨n % size,Nat.mod_lt _ positive⟩
    simpa only [Array.getElem?_eq_getElem inside,Option.some.injEq] using result
  simpa only [size_eq,selected,Nat.cast_zero,Nat.zero_mul,Nat.add_zero] using
    periodic_get values count 0 n (by rw [size_eq]; exact positive) (by rw [size_eq]; exact bound)

private theorem periodic_partition (a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 : Array Nat)
    (size1 : a1.size = 2)
    (size2 : a2.size = 4)
    (size3 : a3.size = 8)
    (size4 : a4.size = 16)
    (size5 : a5.size = 32)
    (size6 : a6.size = 64)
    (size7 : a7.size = 128)
    (size8 : a8.size = 256)
    (size9 : a9.size = 512)
    (size10 : a10.size = 1024)
    (stored1 : ∀ j : Fin 2, a1[j.val]? = some (((j.val + 1) % 2) * 32768))
    (stored2 : ∀ j : Fin 4, a2[j.val]? = some (((j.val + 1) % 4) * 16384))
    (stored3 : ∀ j : Fin 8, a3[j.val]? = some (((j.val + 1) % 8) * 8192))
    (stored4 : ∀ j : Fin 16, a4[j.val]? = some (((j.val + 1) % 16) * 4096))
    (stored5 : ∀ j : Fin 32, a5[j.val]? = some (((j.val + 1) % 32) * 2048))
    (stored6 : ∀ j : Fin 64, a6[j.val]? = some (((j.val + 1) % 64) * 1024))
    (stored7 : ∀ j : Fin 128, a7[j.val]? = some (((j.val + 1) % 128) * 512))
    (stored8 : ∀ j : Fin 256, a8[j.val]? = some (((j.val + 1) % 256) * 256))
    (stored9 : ∀ j : Fin 512, a9[j.val]? = some (((j.val + 1) % 512) * 128))
    (stored10 : ∀ j : Fin 1024, a10[j.val]? = some (((j.val + 1) % 1024) * 64))
    : checkBlocks srlHighLowOutput 0 [.affine 65537 0 0, .periodic 32768 0 a1, .periodic 16384 0 a2, .periodic 8192 0 a3, .periodic 4096 0 a4, .periodic 2048 0 a5, .periodic 1024 0 a6, .periodic 512 0 a7, .periodic 256 0 a8, .periodic 128 0 a9, .periodic 64 0 a10] = true := by
  simp only [checkBlocks_cons_iff,checkBlocks_nil,and_true,Block.length,
    size1,size2,size3,size4,size5,size6,size7,size8,size9,size10,Nat.reduceMul,Nat.reduceAdd]
  repeat' apply And.intro
  · intro i
    have inside := i.isLt
    have value : srlHighLowOutput (0 + i.val) = 0 := by
      by_cases before : i.val < 65536
      · have sh : (0 + i.val) / 65536 = 0 := by omega
        rw [srlHighLowOutput,sh]
        norm_num only
        omega
      · have sh : (0 + i.val) / 65536 = 1 := by omega
        rw [srlHighLowOutput,sh]
        norm_num only
        omega
    rw [value]
    simpa using affine_get 65537 0 0 i.val inside
  · intro i
    have inside : i.val < 65536 := by simpa only [Block.length,size1] using i.isLt
    have value : srlHighLowOutput (65537 + i.val) = (((i.val % 2) + 1) % 2) * 32768 := by
      by_cases before : i.val < 65535
      · have sh : (65537 + i.val) / 65536 = 1 := by omega
        rw [srlHighLowOutput,sh]
        norm_num only
        omega
      · have sh : (65537 + i.val) / 65536 = 2 := by omega
        rw [srlHighLowOutput,sh]
        norm_num only
        omega
    rw [value]
    exact periodic_stored_get a1 2 32768 32768 i.val size1 (by decide)
      (by simpa only [Block.length,size1] using inside) stored1
  · intro i
    have inside : i.val < 65536 := by simpa only [Block.length,size2] using i.isLt
    have value : srlHighLowOutput (131073 + i.val) = (((i.val % 4) + 1) % 4) * 16384 := by
      by_cases before : i.val < 65535
      · have sh : (131073 + i.val) / 65536 = 2 := by omega
        rw [srlHighLowOutput,sh]
        norm_num only
        omega
      · have sh : (131073 + i.val) / 65536 = 3 := by omega
        rw [srlHighLowOutput,sh]
        norm_num only
        omega
    rw [value]
    exact periodic_stored_get a2 4 16384 16384 i.val size2 (by decide)
      (by simpa only [Block.length,size2] using inside) stored2
  · intro i
    have inside : i.val < 65536 := by simpa only [Block.length,size3] using i.isLt
    have value : srlHighLowOutput (196609 + i.val) = (((i.val % 8) + 1) % 8) * 8192 := by
      by_cases before : i.val < 65535
      · have sh : (196609 + i.val) / 65536 = 3 := by omega
        rw [srlHighLowOutput,sh]
        norm_num only
        omega
      · have sh : (196609 + i.val) / 65536 = 4 := by omega
        rw [srlHighLowOutput,sh]
        norm_num only
        omega
    rw [value]
    exact periodic_stored_get a3 8 8192 8192 i.val size3 (by decide)
      (by simpa only [Block.length,size3] using inside) stored3
  · intro i
    have inside : i.val < 65536 := by simpa only [Block.length,size4] using i.isLt
    have value : srlHighLowOutput (262145 + i.val) = (((i.val % 16) + 1) % 16) * 4096 := by
      by_cases before : i.val < 65535
      · have sh : (262145 + i.val) / 65536 = 4 := by omega
        rw [srlHighLowOutput,sh]
        norm_num only
        omega
      · have sh : (262145 + i.val) / 65536 = 5 := by omega
        rw [srlHighLowOutput,sh]
        norm_num only
        omega
    rw [value]
    exact periodic_stored_get a4 16 4096 4096 i.val size4 (by decide)
      (by simpa only [Block.length,size4] using inside) stored4
  · intro i
    have inside : i.val < 65536 := by simpa only [Block.length,size5] using i.isLt
    have value : srlHighLowOutput (327681 + i.val) = (((i.val % 32) + 1) % 32) * 2048 := by
      by_cases before : i.val < 65535
      · have sh : (327681 + i.val) / 65536 = 5 := by omega
        rw [srlHighLowOutput,sh]
        norm_num only
        omega
      · have sh : (327681 + i.val) / 65536 = 6 := by omega
        rw [srlHighLowOutput,sh]
        norm_num only
        omega
    rw [value]
    exact periodic_stored_get a5 32 2048 2048 i.val size5 (by decide)
      (by simpa only [Block.length,size5] using inside) stored5
  · intro i
    have inside : i.val < 65536 := by simpa only [Block.length,size6] using i.isLt
    have value : srlHighLowOutput (393217 + i.val) = (((i.val % 64) + 1) % 64) * 1024 := by
      by_cases before : i.val < 65535
      · have sh : (393217 + i.val) / 65536 = 6 := by omega
        rw [srlHighLowOutput,sh]
        norm_num only
        omega
      · have sh : (393217 + i.val) / 65536 = 7 := by omega
        rw [srlHighLowOutput,sh]
        norm_num only
        omega
    rw [value]
    exact periodic_stored_get a6 64 1024 1024 i.val size6 (by decide)
      (by simpa only [Block.length,size6] using inside) stored6
  · intro i
    have inside : i.val < 65536 := by simpa only [Block.length,size7] using i.isLt
    have value : srlHighLowOutput (458753 + i.val) = (((i.val % 128) + 1) % 128) * 512 := by
      by_cases before : i.val < 65535
      · have sh : (458753 + i.val) / 65536 = 7 := by omega
        rw [srlHighLowOutput,sh]
        norm_num only
        omega
      · have sh : (458753 + i.val) / 65536 = 8 := by omega
        rw [srlHighLowOutput,sh]
        norm_num only
        omega
    rw [value]
    exact periodic_stored_get a7 128 512 512 i.val size7 (by decide)
      (by simpa only [Block.length,size7] using inside) stored7
  · intro i
    have inside : i.val < 65536 := by simpa only [Block.length,size8] using i.isLt
    have value : srlHighLowOutput (524289 + i.val) = (((i.val % 256) + 1) % 256) * 256 := by
      by_cases before : i.val < 65535
      · have sh : (524289 + i.val) / 65536 = 8 := by omega
        rw [srlHighLowOutput,sh]
        norm_num only
        omega
      · have sh : (524289 + i.val) / 65536 = 9 := by omega
        rw [srlHighLowOutput,sh]
        norm_num only
        omega
    rw [value]
    exact periodic_stored_get a8 256 256 256 i.val size8 (by decide)
      (by simpa only [Block.length,size8] using inside) stored8
  · intro i
    have inside : i.val < 65536 := by simpa only [Block.length,size9] using i.isLt
    have value : srlHighLowOutput (589825 + i.val) = (((i.val % 512) + 1) % 512) * 128 := by
      by_cases before : i.val < 65535
      · have sh : (589825 + i.val) / 65536 = 9 := by omega
        rw [srlHighLowOutput,sh]
        norm_num only
        omega
      · have sh : (589825 + i.val) / 65536 = 10 := by omega
        rw [srlHighLowOutput,sh]
        norm_num only
        omega
    rw [value]
    exact periodic_stored_get a9 512 128 128 i.val size9 (by decide)
      (by simpa only [Block.length,size9] using inside) stored9
  · intro i
    have inside : i.val < 65536 := by simpa only [Block.length,size10] using i.isLt
    have value : srlHighLowOutput (655361 + i.val) = (((i.val % 1024) + 1) % 1024) * 64 := by
      by_cases before : i.val < 65535
      · have sh : (655361 + i.val) / 65536 = 10 := by omega
        rw [srlHighLowOutput,sh]
        norm_num only
        omega
      · have sh : (655361 + i.val) / 65536 = 11 := by omega
        rw [srlHighLowOutput,sh]
        norm_num only
        omega
    rw [value]
    exact periodic_stored_get a10 1024 64 64 i.val size10 (by decide)
      (by simpa only [Block.length,size10] using inside) stored10

theorem outputs_part0 : checkBlocks srlHighLowOutput 0 part0 = true :=
  Eq.mpr (congrArg (fun blocks => checkBlocks srlHighLowOutput 0 blocks = true) part0_shape)
    (periodic_partition template1 template2 template3 template4 template5 template6 template7 template8 template9 template10
      template1_size template2_size template3_size template4_size template5_size template6_size template7_size template8_size template9_size template10_size
      template1_values template2_values template3_values template4_values template5_values template6_values template7_values template8_values template9_values template10_values)

end Airbender.Verification.SrlHighProofs
