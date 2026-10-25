import Airbender.Proofs.Tables.BlockRanges
import GKRProtocol.MaterializedSetup
import Airbender.Proofs.BabyBear
import Mathlib.Data.List.TakeDrop

namespace Airbender.Compiler
open Airbender
set_option warningAsError true

theorem getFromBlocks_before_suffix (selected tail : List Setup.Block) (index : Nat)
    (bounded : index < (selected.map Setup.Block.length).sum) :
    Setup.getFromBlocks (selected ++ tail) index = Setup.getFromBlocks selected index := by
  induction selected generalizing index with
  | nil => simp at bounded
  | cons block rest ih =>
    simp only [List.map_cons, List.sum_cons] at bounded
    simp only [List.cons_append, Setup.getFromBlocks]
    split
    · rfl
    · exact ih _ (by omega)

/-- Aligned imported block slices preserve every selected row. Prefix/suffix
contents are retained as literal proof data; no table-generation recipe is used. -/
theorem column_slice_value (full selected : Setup.Column) (front back : List Setup.Block)
    (offset length : Nat)
    (shape : full.blocks.toList = front ++ (selected.blocks.toList ++ back))
    (prefixLength : (front.map Setup.Block.length).sum = offset)
    (sliceLength : (selected.blocks.toList.map Setup.Block.length).sum = length)
    (index : Nat) (bounded : index < length) :
    full.get? (offset + index) = selected.get? index := by
  simp only [Setup.Column.get?]
  rw [shape, ← prefixLength, Setup.Proofs.skip_blocks]
  exact getFromBlocks_before_suffix _ _ index (by rw [sliceLength]; exact bounded)

theorem column_block_value (column : Setup.Column) (block : Fin column.blocks.size)
    (offset index : Nat)
    (prefixLength : ((column.blocks.toList.take block.val).map Setup.Block.length).sum = offset)
    (lower : offset ≤ index) (bounded : index - offset < column.blocks[block.val].length) :
    column.get? index = column.blocks[block.val].get? (index - offset) := by
  simp only [Setup.Column.get?]
  rw [← List.take_append_drop block.val column.blocks.toList,
    List.drop_eq_getElem_cons (by exact block.isLt)]
  exact Setup.Proofs.selected_at _ _ _ offset index prefixLength lower bounded

theorem constant_block_get (length value index : Nat) (bounded : index < length) :
    (Setup.Block.affine length value 0).get? index = some value := by
  simp [Setup.Block.get?, Setup.Block.length, bounded]

theorem periodic_block_overlap (left right : Nat) (stride : Int) (values : Array Nat)
    (index : Nat) (leftBound : index < left * values.size) (rightBound : index < right * values.size) :
    (Setup.Block.periodic left stride values).get? index =
      (Setup.Block.periodic right stride values).get? index := by
  simp only [Setup.Block.get?, Setup.Block.length, if_pos leftBound, if_pos rightBound]

theorem MaterializedLookupSetup.generic_cell_value (native : MaterializedLookupSetup width)
    (row : Fin native.imported.data.length) (column : Fin width) :
    native.value row (.generic column.val) =
      (((native.imported.data.columns[column.val]).get?
        (native.imported.data.offset + row.val)).getD 0 : Source.BaseField) := by
  rw [native.value_generic]
  simp only [Setup.TableData.row, Vector.getElem_map]
  exact Setup.signedValue_cast _

end Airbender.Compiler
