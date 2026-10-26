import Airbender.Proofs.GKRProtocol.ROMParts.Unified.Column3.Part0
import Airbender.Import.GKRProtocol.BlockCoverageImport
import Airbender.Proofs.GKRProtocol.ColumnSlices
import Airbender.Data.GKRSetup.Unified

namespace Airbender.Compiler.ROMColumns.Unified.Column3
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

column_blocks_part selected from Data.GKRSetup.Unified.setupColumn3 start 1 stop 3
column_blocks_part back from Data.GKRSetup.Unified.setupColumn3 start 3 stop 6

column_parts_cover sourceCoverage from Data.GKRSetup.Unified.setupColumn3 parts [front0, selected, back]

noncomputable def front : List Setup.Block := ([front0] : List (List Setup.Block)).flatten

noncomputable def selectedColumn : Setup.Column := ⟨selected.toArray⟩

theorem prefixLength : (front.map Setup.Block.length).sum = 327938 := by
  simp only [front, List.flatten_cons, List.flatten_nil, List.map_append, List.sum_append, List.map_nil, List.sum_nil, frontLength0]
  decide +kernel

theorem selectedLength : (selectedColumn.blocks.toList.map Setup.Block.length).sum = 1769602 := by decide +kernel

theorem sourceShape : Data.GKRSetup.Unified.setupColumn3.blocks.toList = front ++ (selectedColumn.blocks.toList ++ back) := by
  rw [sourceCoverage]
  simp only [front, selectedColumn, List.toList_toArray, List.flatten_cons, List.flatten_nil, List.append_nil]

theorem column_value (index : Fin 1048576) :
    Data.GKRSetup.Unified.setupColumn3.get? (590081 + index.val) = selectedColumn.get? (262143 + index.val) := by
  have actual := column_slice_value Data.GKRSetup.Unified.setupColumn3 selectedColumn front back 327938 1769602
    sourceShape prefixLength selectedLength (262143 + index.val) (by have := index.isLt; omega)
  simpa only [show 327938 + (262143 + index.val) = 590081 + index.val by omega] using actual

end Airbender.Compiler.ROMColumns.Unified.Column3
