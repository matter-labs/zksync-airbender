import Airbender.Proofs.Tables.UniformBlocks
import Airbender.Proofs.Tables.BlockRanges
import Airbender.Proofs.FullUnsigned.SetupSourceArrays

namespace Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false

/-- A row inside a retained prefix does not read the suffix. -/
theorem getFromBlocks_append_left (front back : List Block) (index : Nat)
    (bound : index < (front.map Block.length).sum) :
    getFromBlocks (front ++ back) index = getFromBlocks front index := by
  induction front generalizing index with
  | nil => simp at bound
  | cons block rest ih =>
    simp only [List.map_cons, List.sum_cons] at bound
    simp only [List.cons_append, getFromBlocks]
    split
    · rfl
    · exact ih (index - block.length) (by omega)

/-- Select an exact source block prefix without expanding unrelated blocks. -/
theorem getFromBlocks_take (blocks : List Block) (count index : Nat)
    (bound : index < ((blocks.take count).map Block.length).sum) :
    getFromBlocks blocks index = getFromBlocks (blocks.take count) index := by
  conv_lhs => rw [← List.take_append_drop count blocks]
  exact getFromBlocks_append_left _ _ index bound

/-- Native 65,536-row chunks select one stored block and its local row. -/
theorem uniform65536_get (blocks : List Block)
    (shape : ∀ block ∈ blocks, block.length = 65536) (n : Nat) :
    getFromBlocks blocks n =
      (blocks[n / 65536]?).bind (fun block => block.get? (n % 65536)) := by
  induction blocks generalizing n with
  | nil => rfl
  | cons block rest ih =>
    have head := shape block (by simp)
    have tail : ∀ b ∈ rest, b.length = 65536 := fun b member => shape b (by simp [member])
    by_cases inside : n < 65536
    · rw [getFromBlocks, head, if_pos inside]
      simp only [Nat.div_eq_of_lt inside, Nat.mod_eq_of_lt inside,
        List.getElem?_cons_zero, Option.bind_some]
    · have quot : n / 65536 = (n - 65536) / 65536 + 1 := by omega
      have residue : n % 65536 = (n - 65536) % 65536 := by omega
      rw [getFromBlocks, head, if_neg inside, ih tail (n - 65536), quot,
        List.getElem?_cons_succ, residue]

theorem constant_affine_get (length value index : Nat) (bound : index < length) :
    Block.get? (.affine length value 0) index = some value := by
  simp only [Block.get?, Block.length, if_pos bound, zero_mul, add_zero,
    if_pos (Int.natCast_nonneg value), Int.toNat_natCast]

/-- Complete coverage locates any retained source suffix. -/
theorem column_suffix_get (column : Column) (first length index : Nat)
    (covered : (column.blocks.toList.map Block.length).sum = length)
    (lower : length - ((column.blocks.toList.drop first).map Block.length).sum ≤ index) :
    column.get? index = getFromBlocks (column.blocks.toList.drop first)
      (index - (length - ((column.blocks.toList.drop first).map Block.length).sum)) := by
  let front := column.blocks.toList.take first
  let back := column.blocks.toList.drop first
  have partition : column.blocks.toList = front ++ back := (List.take_append_drop first _).symm
  have total := covered
  rw [partition, List.map_append, List.sum_append] at total
  have start : (front.map Block.length).sum = length - (back.map Block.length).sum := by omega
  have splitIndex : index = (front.map Block.length).sum + (index - (front.map Block.length).sum) := by
    change length - (back.map Block.length).sum ≤ index at lower
    omega
  change getFromBlocks column.blocks.toList index =
    getFromBlocks back (index - (length - (back.map Block.length).sum))
  conv_lhs => rw [partition, splitIndex, skip_blocks]
  rw [start]

end Airbender.Setup.Proofs
