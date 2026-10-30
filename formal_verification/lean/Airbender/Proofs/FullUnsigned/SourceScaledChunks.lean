import Airbender.Proofs.FullUnsigned.SourceBlockScaling

namespace Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false

private def scaledValues (scale : Nat) (values : Array Nat) : Array Nat :=
  (values.toList.flatMap fun value => List.replicate scale value).toArray

private theorem repeated_length (scale : Nat) (values : List Nat) :
    (values.flatMap fun value => List.replicate scale value).length = scale * values.length := by
  induction values with
  | nil => simp only [List.flatMap_nil, List.length_nil, Nat.mul_zero]
  | cons value rest ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_replicate, ih,
      List.length_cons, Nat.mul_succ, Nat.add_comm]

private theorem repeated_get (scale : Nat) (positive : 0 < scale) (values : List Nat) (index : Nat) :
    (values.flatMap fun value => List.replicate scale value)[index]? = values[index / scale]? := by
  induction values generalizing index with
  | nil => rfl
  | cons value rest ih =>
    simp only [List.flatMap_cons]
    by_cases inside : index < scale
    · rw [List.getElem?_append_left (by simpa only [List.length_replicate] using inside),
        List.getElem?_replicate_of_lt inside, Nat.div_eq_of_lt inside, List.getElem?_cons_zero]
    · rw [List.getElem?_append_right (by simpa only [List.length_replicate] using (by omega : scale ≤ index)),
        List.length_replicate, ih]
      have shifted : index = scale + (index - scale) := by omega
      have quotient : index / scale = (index - scale) / scale + 1 := by
        conv_lhs => rw [shifted, Nat.add_div_left _ positive]
      rw [quotient, List.getElem?_cons_succ]

private theorem scaledValues_size (scale : Nat) (values : Array Nat) :
    (scaledValues scale values).size = scale * values.size := by
  simp only [scaledValues, List.size_toArray, repeated_length, Array.length_toList]

private theorem scaledValues_get (scale : Nat) (positive : 0 < scale) (values : Array Nat) (index : Nat) :
    (scaledValues scale values)[index]? = values[index / scale]? := by
  simp only [scaledValues, List.getElem?_toArray, repeated_get scale positive, Array.getElem?_toList]

/-- Expand constant chunks by a specified number of physical rows. -/
def ChunkBlock.expandBy (scale : Nat) : ChunkBlock → Block
  | .constant length value => .affine (scale * length) value 0
  | .periodic count stride values => .periodic count stride (scaledValues scale values)

theorem ChunkBlock.expandBy_length (scale : Nat) (block : ChunkBlock) :
    (block.expandBy scale).length = scale * block.compact.length := by
  cases block <;> simp [expandBy, compact, Block.length, scaledValues_size, Nat.mul_left_comm]

theorem ChunkBlock.expandBy_get (scale : Nat) (positive : 0 < scale) (block : ChunkBlock) (index : Nat)
    (bound : index < (block.expandBy scale).length) :
    (block.expandBy scale).get? index = block.compact.get? (index / scale) := by
  cases block with
  | constant length value =>
    have small : index / scale < length := (Nat.div_lt_iff_lt_mul positive).mpr
      (by simpa only [expandBy, Block.length, Nat.mul_comm] using bound)
    exact (constant_affine_get _ _ _ bound).trans (constant_affine_get _ _ _ small).symm
  | periodic count stride values =>
    have inside : index < count * (scale * values.size) := by
      simpa only [expandBy, Block.length, scaledValues_size] using bound
    have small : index / scale < count * values.size := (Nat.div_lt_iff_lt_mul positive).mpr
      (by simpa only [Nat.mul_assoc, Nat.mul_comm scale values.size] using inside)
    have residue : index % (scale * values.size) / scale = index / scale % values.size :=
      Nat.mod_mul_right_div_self _ _ _
    have quotient : index / (scale * values.size) = index / scale / values.size := by
      rw [Nat.div_div_eq_div_mul]
    change Block.get? (.periodic count stride _) index = Block.get? (.periodic count stride values) (index / scale)
    simp only [Block.get?, Block.length, scaledValues_size, if_pos inside, if_pos small,
      scaledValues_get scale positive, residue, ← Int.natCast_ediv, quotient]

theorem expanded_blocks_length (scale : Nat) (blocks : List ChunkBlock) :
    ((blocks.map (ChunkBlock.expandBy scale)).map Block.length).sum =
      scale * ((blocks.map ChunkBlock.compact).map Block.length).sum := by
  simp only [List.map_map, Function.comp_def, ChunkBlock.expandBy_length, List.sum_map_mul_left]

/-- Read a scaled chunk list without evaluating its repeated physical rows. -/
theorem getFromBlocks_expandBy (scale : Nat) (positive : 0 < scale) (blocks : List ChunkBlock) (index : Nat) :
    getFromBlocks (blocks.map (ChunkBlock.expandBy scale)) index =
      getFromBlocks (blocks.map ChunkBlock.compact) (index / scale) := by
  induction blocks generalizing index with
  | nil => rfl
  | cons block rest ih =>
    simp only [List.map_cons, getFromBlocks]
    by_cases inside : index < (block.expandBy scale).length
    · have small : index / scale < block.compact.length := (Nat.div_lt_iff_lt_mul positive).mpr
        (by simpa only [ChunkBlock.expandBy_length, Nat.mul_comm] using inside)
      rw [if_pos inside, if_pos small, ChunkBlock.expandBy_get _ positive _ _ inside]
    · have outside : ¬ index / scale < block.compact.length := by
        rw [Nat.div_lt_iff_lt_mul positive]
        simpa only [ChunkBlock.expandBy_length, Nat.mul_comm] using inside
      have offset : (index - (block.expandBy scale).length) / scale = index / scale - block.compact.length := by
        rw [ChunkBlock.expandBy_length]
        exact Nat.sub_mul_div_of_le index scale block.compact.length (by
          rw [ChunkBlock.expandBy_length] at inside; omega)
      rw [if_neg inside, if_neg outside, ih, offset]

end Airbender.Setup.Proofs
