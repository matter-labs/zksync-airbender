import GKRProtocol.BlockCoverageImport
import GKRProtocol.ColumnSlices
import Airbender.Data.GKRSetup.Unified

namespace Airbender.Compiler.ROMColumns.Unified.Column8
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

column_blocks_part selected from Data.GKRSetup.Unified.setupColumn8 start 0 stop 1
column_blocks_part back from Data.GKRSetup.Unified.setupColumn8 start 1 stop 4

column_parts_cover sourceCoverage from Data.GKRSetup.Unified.setupColumn8 parts [selected, back]

noncomputable def front : List Setup.Block := ([] : List (List Setup.Block)).flatten

noncomputable def selectedColumn : Setup.Column := ⟨selected.toArray⟩

theorem prefixLength : (front.map Setup.Block.length).sum = 0 := by
  rfl

theorem selectedLength : (selectedColumn.blocks.toList.map Setup.Block.length).sum = 2097537 := by decide +kernel

theorem sourceShape : Data.GKRSetup.Unified.setupColumn8.blocks.toList = front ++ (selectedColumn.blocks.toList ++ back) := by
  rw [sourceCoverage]
  simp only [front, selectedColumn, List.toList_toArray, List.flatten_cons, List.flatten_nil, List.nil_append, List.append_nil]

theorem column_value (index : Fin 1048576) :
    Data.GKRSetup.Unified.setupColumn8.get? (590081 + index.val) = selectedColumn.get? (590081 + index.val) := by
  have actual := column_slice_value Data.GKRSetup.Unified.setupColumn8 selectedColumn front back 0 2097537
    sourceShape prefixLength selectedLength (590081 + index.val) (by have := index.isLt; omega)
  simpa only [show 0 + (590081 + index.val) = 590081 + index.val by omega] using actual

end Airbender.Compiler.ROMColumns.Unified.Column8
