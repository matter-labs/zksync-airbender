import Airbender.Proofs.FullUnsigned.SourceColumnRanges

namespace Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Skip a constant prefix inside the first source block. -/
theorem skip_constant_head (length value skip index : Nat) (rest : List Block)
    (inside : skip ≤ length) :
    getFromBlocks (.affine length value 0 :: rest) (skip + index) =
      getFromBlocks (.affine (length - skip) value 0 :: rest) index := by
  by_cases bound : index < length - skip
  · have large : skip + index < length := by omega
    simp only [getFromBlocks, Block.length, ite_eq_left large, ite_eq_left bound]
    exact (constant_affine_get _ _ _ large).trans (constant_affine_get _ _ _ bound).symm
  · have outside : ¬ skip + index < length := by omega
    simp only [getFromBlocks, Block.length, ite_eq_right outside, ite_eq_right bound]
    congr 1
    omega

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Rows below a shortened constant tail keep their exact source values. -/
theorem shorten_constant_tail (front : List Block) (length extra value index : Nat)
    (bound : index < (front.map Block.length).sum + length) :
    getFromBlocks (front ++ [.affine (length + extra) value 0]) index =
      getFromBlocks (front ++ [.affine length value 0]) index := by
  induction front generalizing index with
  | nil =>
    have small : index < length := by simpa only [List.map_nil, List.sum_nil, Nat.zero_add] using bound
    have large : index < length + extra := by omega
    simp only [List.nil_append, getFromBlocks, Block.length, ite_eq_left large, ite_eq_left small]
    exact (constant_affine_get _ _ _ large).trans (constant_affine_get _ _ _ small).symm
  | cons block rest ih =>
    simp only [List.map_cons, List.sum_cons] at bound
    simp only [List.cons_append, getFromBlocks]
    split
    · rfl
    · apply ih
      omega

end Airbender.Setup.Proofs
