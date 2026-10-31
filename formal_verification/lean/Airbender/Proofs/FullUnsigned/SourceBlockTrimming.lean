import Airbender.Proofs.FullUnsigned.SourceColumnRanges

namespace Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false

/-- Skip a constant prefix inside the first source block. -/
theorem skip_constant_head (length value skip index : Nat) (rest : List Block)
    (inside : skip ≤ length) :
    getFromBlocks (.affine length value 0 :: rest) (skip + index) =
      getFromBlocks (.affine (length - skip) value 0 :: rest) index := by
  by_cases bound : index < length - skip
  · have large : skip + index < length := by omega
    simp only [getFromBlocks, Block.length, if_pos large, if_pos bound]
    exact (constant_affine_get _ _ _ large).trans (constant_affine_get _ _ _ bound).symm
  · have outside : ¬ skip + index < length := by omega
    simp only [getFromBlocks, Block.length, if_neg outside, if_neg bound]
    congr 1
    omega

/-- Rows below a shortened constant tail keep their exact source values. -/
theorem shorten_constant_tail (front : List Block) (length extra value index : Nat)
    (bound : index < (front.map Block.length).sum + length) :
    getFromBlocks (front ++ [.affine (length + extra) value 0]) index =
      getFromBlocks (front ++ [.affine length value 0]) index := by
  induction front generalizing index with
  | nil =>
    have small : index < length := by simpa only [List.map_nil, List.sum_nil, Nat.zero_add] using bound
    have large : index < length + extra := by omega
    simp only [List.nil_append, getFromBlocks, Block.length, if_pos large, if_pos small]
    exact (constant_affine_get _ _ _ large).trans (constant_affine_get _ _ _ small).symm
  | cons block rest ih =>
    simp only [List.map_cons, List.sum_cons] at bound
    simp only [List.cons_append, getFromBlocks]
    split
    · rfl
    · apply ih
      omega

end Airbender.Setup.Proofs
