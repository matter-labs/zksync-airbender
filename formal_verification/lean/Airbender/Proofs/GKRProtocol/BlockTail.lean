import Airbender.Proofs.GKRProtocol.ChunkLengths

namespace Airbender.Compiler
set_option warningAsError true

theorem block_suffix_congr (left right tail : List Setup.Block)
    (lengths : (left.map Setup.Block.length).sum = (right.map Setup.Block.length).sum)
    (values : ∀ index, Setup.getFromBlocks left index = Setup.getFromBlocks right index)
    (index : Nat) : Setup.getFromBlocks (left ++ tail) index = Setup.getFromBlocks (right ++ tail) index := by
  rw [getFromBlocks_append, getFromBlocks_append, lengths]
  split
  · exact values index
  · rfl

theorem column_tail_value (column : Setup.Column)
    (sourceParts regionParts extra suffix : List Setup.Block) (offset : Nat)
    (sourceShape : column.blocks.toList = sourceParts ++ suffix)
    (lengths : (sourceParts.map Setup.Block.length).sum = ((regionParts ++ extra).map Setup.Block.length).sum)
    (values : ∀ index, Setup.getFromBlocks sourceParts index = Setup.getFromBlocks (regionParts ++ extra) index)
    (regionLength : (regionParts.map Setup.Block.length).sum = offset) (index : Nat) :
    column.get? (offset + index) = Setup.getFromBlocks (extra ++ suffix) index := by
  change Setup.getFromBlocks column.blocks.toList (offset + index) = _
  rw [sourceShape, block_suffix_congr sourceParts (regionParts ++ extra) suffix lengths values,
    List.append_assoc]
  have skipped := Setup.Proofs.skip_blocks regionParts (extra ++ suffix) index
  rw [regionLength] at skipped
  exact skipped

end Airbender.Compiler
