import Airbender.Proofs.Tables.PeriodicColumns

namespace Airbender.ReducedMachine.ShiftBlockProofs
open Setup
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

theorem get_append (left right : List Block) (n : Nat) :
    getFromBlocks (left ++ right) n =
      if n < (left.map Block.length).sum then getFromBlocks left n
      else getFromBlocks right (n - (left.map Block.length).sum) := by
  induction left generalizing n with
  | nil => simp
  | cons block rest ih =>
    simp only [List.cons_append,List.map_cons,List.sum_cons]
    by_cases first : n < block.length
    · have total : n < block.length + (rest.map Block.length).sum := by omega
      rw [getFromBlocks,if_pos first,if_pos total,getFromBlocks,if_pos first]
    · have relation : n - block.length < (rest.map Block.length).sum ↔
          n < block.length + (rest.map Block.length).sum := by omega
      rw [getFromBlocks,if_neg first,ih]
      simp only [relation]
      split
      · rw [getFromBlocks,if_neg first]
      · simp only [Nat.sub_sub]

private theorem zero_get (length n : Nat) (bound : n < length) :
    Block.get? (.affine length 0 0) n = some 0 := by
  simp [Block.get?,Block.length,bound]

private theorem sequence_get (length first n : Nat) (bound : n < length) :
    Block.get? (.affine length first 1) n = some (first + n) := by
  simp only [Block.get?,Block.length,if_pos bound,one_mul]
  have casts : (first : Int) + n = ((first + n : Nat) : Int) := by simp
  rw [casts,if_pos (Int.natCast_nonneg _),Int.toNat_natCast]

/-- Native compression joins the last left-shift zeros with the first zero
    of right-shift input zero. This proves that exact boundary resegmentation. -/
theorem native_boundary (zeros count : Nat) (positive : 0 < count)
    (tail : List Block) (n : Nat) :
    getFromBlocks (.affine (zeros + 1) 0 0 :: .affine (count - 1) 1 1 :: tail) n =
      getFromBlocks (.affine zeros 0 0 :: .affine count 0 1 :: tail) n := by
  by_cases left : n < zeros
  · have merged : n < zeros + 1 := by omega
    simp only [getFromBlocks,Block.length,if_pos merged,if_pos left]
    rw [zero_get (zeros + 1) n merged,zero_get zeros n left]
  · by_cases edge : n = zeros
    · subst n
      have merged : zeros < zeros + 1 := by omega
      simp only [getFromBlocks,Block.length,if_pos merged,Nat.lt_irrefl,if_false,Nat.sub_self,if_pos positive]
      rw [zero_get (zeros + 1) zeros merged,sequence_get count 0 0 positive]
    · have merged : ¬ n < zeros + 1 := by omega
      by_cases inside : n < zeros + count
      · have newInside : n - (zeros + 1) < count - 1 := by omega
        have oldInside : n - zeros < count := by omega
        simp only [getFromBlocks,Block.length,if_neg merged,if_neg left,if_pos newInside,if_pos oldInside]
        rw [sequence_get (count - 1) 1 (n - (zeros + 1)) newInside,sequence_get count 0 (n - zeros) oldInside]
        congr 1
        omega
      · have newOutside : ¬ n - (zeros + 1) < count - 1 := by omega
        have oldOutside : ¬ n - zeros < count := by omega
        simp only [getFromBlocks,Block.length,if_neg merged,if_neg left,if_neg newOutside,if_neg oldOutside]
        congr 1
        omega

end Airbender.ReducedMachine.ShiftBlockProofs
