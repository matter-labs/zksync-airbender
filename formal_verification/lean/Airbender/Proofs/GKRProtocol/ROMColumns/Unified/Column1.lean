import Airbender.Proofs.GKRProtocol.ROMParts.Unified.Column1.Part0
import Airbender.Import.GKRProtocol.BlockCoverageImport
import Airbender.Proofs.GKRProtocol.ColumnSlices
import Airbender.Data.GKRSetup.Unified

namespace Airbender.Compiler.ROMColumns.Unified.Column1
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

column_blocks_part selected from Data.GKRSetup.Unified.setupColumn1 start 12 stop 14
column_blocks_part back from Data.GKRSetup.Unified.setupColumn1 start 14 stop 37

column_parts_cover sourceCoverage from Data.GKRSetup.Unified.setupColumn1 parts [front0, selected, back]

noncomputable def front : List Setup.Block := ([front0] : List (List Setup.Block)).flatten

noncomputable def selectedColumn : Setup.Column := ⟨selected.toArray⟩

theorem prefixLength : (front.map Setup.Block.length).sum = 590081 := by
  simp only [front, List.flatten_cons, List.flatten_nil, List.map_append, List.sum_append, List.map_nil, List.sum_nil, frontLength0]
  decide +kernel

theorem selectedLength : (selectedColumn.blocks.toList.map Setup.Block.length).sum = 1048577 := by decide +kernel

theorem sourceShape : Data.GKRSetup.Unified.setupColumn1.blocks.toList = front ++ (selectedColumn.blocks.toList ++ back) := by
  rw [sourceCoverage]
  simp only [front, selectedColumn, List.toList_toArray, List.flatten_cons, List.flatten_nil, List.append_nil]

theorem column_value (index : Fin 1048576) :
    Data.GKRSetup.Unified.setupColumn1.get? (590081 + index.val) = selectedColumn.get? (0 + index.val) := by
  have actual := column_slice_value Data.GKRSetup.Unified.setupColumn1 selectedColumn front back 590081 1048577
    sourceShape prefixLength selectedLength (0 + index.val) (by have := index.isLt; omega)
  simpa only [show 590081 + (0 + index.val) = 590081 + index.val by omega] using actual

end Airbender.Compiler.ROMColumns.Unified.Column1
