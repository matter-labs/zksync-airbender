import Airbender.Import.SetupEmbed
import Lean.Elab.Tactic.Omega

namespace Airbender.Setup.Proofs
set_option warningAsError true

/-- Skip a complete prefix without unfolding its stored field values. -/
theorem getFromBlocks_append (before after : List Block) (index : Nat) :
    getFromBlocks (before ++ after) ((before.map Block.length).sum + index) =
      getFromBlocks after index := by
  induction before with
  | nil => simp only [List.nil_append, List.map_nil, List.sum_nil, Nat.zero_add]
  | cons first rest ih =>
    simp only [List.cons_append, List.map_cons, List.sum_cons, getFromBlocks]
    rw [if_neg (by omega)]
    rw [show first.length + (rest.map Block.length).sum + index - first.length =
      (rest.map Block.length).sum + index by omega]
    exact ih

/-- Offset lookup in appended columns depends only on the suffix. -/
theorem column_append_shift (before after : Column) (offset index : Nat)
    (length : (before.blocks.toList.map Block.length).sum = offset) :
    (Column.mk (before.blocks ++ after.blocks)).get? (offset + index) = after.get? index := by
  simp only [Column.get?, Array.toList_append]
  rw [← length]
  exact getFromBlocks_append _ _ _

end Airbender.Setup.Proofs
