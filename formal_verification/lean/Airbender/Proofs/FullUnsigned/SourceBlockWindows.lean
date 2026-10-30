import Airbender.Proofs.FullUnsigned.SourceColumnRanges

namespace Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false

/-- An exact block window preserves its physical row offset. -/
theorem getFromBlocks_window (blocks : List Block) (first count start index : Nat)
    (offset : ((blocks.take first).map Block.length).sum = start)
    (bound : index < (((blocks.drop first).take count).map Block.length).sum) :
    getFromBlocks blocks (start + index) = getFromBlocks ((blocks.drop first).take count) index := by
  conv_lhs => rw [← List.take_append_drop first blocks, ← offset, skip_blocks]
  exact getFromBlocks_take _ _ _ bound

end Airbender.Setup.Proofs
