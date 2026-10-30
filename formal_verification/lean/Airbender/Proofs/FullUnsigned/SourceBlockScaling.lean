import Airbender.Proofs.FullUnsigned.SourceColumnRanges
import Airbender.Proofs.Tables.PeriodicColumns

namespace Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false

/-- A short block whose values each occupy 256 physical rows. -/
inductive ChunkBlock where
  | constant (length value : Nat)
  | periodic (count : Nat) (stride : Int) (values : Array Nat)

def ChunkBlock.compact : ChunkBlock → Block
  | .constant length value => .affine length value 0
  | .periodic count stride values => .periodic count stride values

private def expandedValues (values : Array Nat) : Array Nat :=
  (values.toList.flatMap fun value => List.replicate 256 value).toArray

private theorem repeated_length (values : List Nat) :
    (values.flatMap fun value => List.replicate 256 value).length = 256 * values.length := by
  induction values with
  | nil => rfl
  | cons value rest ih => simp only [List.flatMap_cons, List.length_append,
      List.length_replicate, ih, List.length_cons]; omega

private theorem repeated_get (values : List Nat) (index : Nat) :
    (values.flatMap fun value => List.replicate 256 value)[index]? = values[index / 256]? := by
  induction values generalizing index with
  | nil => rfl
  | cons value rest ih =>
    simp only [List.flatMap_cons]
    by_cases inside : index < 256
    · rw [List.getElem?_append_left (by simpa only [List.length_replicate] using inside)]
      rw [List.getElem?_replicate_of_lt inside, Nat.div_eq_of_lt inside, List.getElem?_cons_zero]
    · rw [List.getElem?_append_right (by simpa only [List.length_replicate] using (by omega : 256 ≤ index)),
        List.length_replicate, ih]
      have quotient : index / 256 = (index - 256) / 256 + 1 := by omega
      rw [quotient, List.getElem?_cons_succ]

private theorem expandedValues_size (values : Array Nat) :
    (expandedValues values).size = 256 * values.size := by
  simp only [expandedValues, List.size_toArray, repeated_length, Array.length_toList]

private theorem expandedValues_get (values : Array Nat) (index : Nat) :
    (expandedValues values)[index]? = values[index / 256]? := by
  simp only [expandedValues, List.getElem?_toArray, repeated_get, Array.getElem?_toList]

def ChunkBlock.expand : ChunkBlock → Block
  | .constant length value => .affine (256 * length) value 0
  | .periodic count stride values => .periodic count stride (expandedValues values)

theorem ChunkBlock.expand_length (block : ChunkBlock) :
    block.expand.length = 256 * block.compact.length := by
  cases block <;> simp [expand, compact, Block.length, expandedValues_size, Nat.mul_left_comm]

theorem ChunkBlock.expand_get (block : ChunkBlock) (index : Nat)
    (bound : index < block.expand.length) :
    block.expand.get? index = block.compact.get? (index / 256) := by
  cases block with
  | constant length value =>
    have small : index / 256 < length := by
      change index < 256 * length at bound
      omega
    exact (constant_affine_get _ _ _ bound).trans (constant_affine_get _ _ _ small).symm
  | periodic count stride values =>
    have inside : index < count * (256 * values.size) := by
      simpa only [expand, Block.length, expandedValues_size] using bound
    have small : index / 256 < count * values.size := by
      have scaled : index < 256 * (count * values.size) := by
        simpa only [Nat.mul_left_comm] using inside
      omega
    have residue : index % (256 * values.size) / 256 = index / 256 % values.size :=
      Nat.mod_mul_right_div_self _ _ _
    have quotient : index / (256 * values.size) = index / 256 / values.size := by
      rw [Nat.div_div_eq_div_mul]
    change Block.get? (.periodic count stride _) index =
      Block.get? (.periodic count stride values) (index / 256)
    simp only [Block.get?, Block.length, expandedValues_size, if_pos inside, if_pos small,
      expandedValues_get, residue, ← Int.natCast_ediv, quotient]

/-- Chunk expansion preserves every physical row, including the end of a list. -/
theorem getFromBlocks_expand (blocks : List ChunkBlock) (index : Nat) :
    getFromBlocks (blocks.map ChunkBlock.expand) index =
      getFromBlocks (blocks.map ChunkBlock.compact) (index / 256) := by
  induction blocks generalizing index with
  | nil => rfl
  | cons block rest ih =>
    simp only [List.map_cons, getFromBlocks]
    by_cases inside : index < block.expand.length
    · have small : index / 256 < block.compact.length := by
        rw [ChunkBlock.expand_length] at inside
        omega
      rw [if_pos inside, if_pos small, ChunkBlock.expand_get _ _ inside]
    · have outside : ¬ index / 256 < block.compact.length := by
        rw [ChunkBlock.expand_length] at inside
        omega
      have offset : (index - block.expand.length) / 256 = index / 256 - block.compact.length := by
        rw [ChunkBlock.expand_length]
        omega
      rw [if_neg inside, if_neg outside, ih, offset]

/-- Check each short block at its absolute row offset. -/
def checkBlockRows (expected : Nat → Nat) : Nat → List Block → Bool
  | _, [] => true
  | first, block :: rest =>
      ((List.range block.length).all fun offset =>
        block.get? offset == some (expected (first + offset))) &&
      checkBlockRows expected (first + block.length) rest

/-- A successful finite block check supplies every row in its covered interval. -/
theorem checkBlockRows_sound (expected : Nat → Nat) (blocks : List Block) (first index : Nat)
    (checked : checkBlockRows expected first blocks = true)
    (bound : index < (blocks.map Block.length).sum) :
    getFromBlocks blocks index = some (expected (first + index)) := by
  induction blocks generalizing first index with
  | nil => simp at bound
  | cons block rest ih =>
    simp only [checkBlockRows, Bool.and_eq_true] at checked
    simp only [getFromBlocks]
    by_cases inside : index < block.length
    · rw [if_pos inside]
      exact beq_iff_eq.mp ((List.all_eq_true.mp checked.1) index (List.mem_range.mpr inside))
    · rw [if_neg inside]
      have remaining : index - block.length < (rest.map Block.length).sum := by
        simp only [List.map_cons, List.sum_cons] at bound
        omega
      have next := ih (first + block.length) (index - block.length) checked.2 remaining
      have offset : first + block.length + (index - block.length) = first + index := by omega
      simpa only [offset] using next

end Airbender.Setup.Proofs
