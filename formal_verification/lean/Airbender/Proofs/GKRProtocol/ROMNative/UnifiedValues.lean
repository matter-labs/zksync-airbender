import Airbender.Proofs.GKRProtocol.ROMColumns.Unified.Column0
import Airbender.Proofs.GKRProtocol.ROMColumns.Unified.Column1
import Airbender.Proofs.GKRProtocol.ROMColumns.Unified.Column2
import Airbender.Proofs.GKRProtocol.ROMColumns.Unified.Column3
import Airbender.Proofs.GKRProtocol.ROMColumns.Unified.Column4
import Airbender.Proofs.GKRProtocol.ROMColumns.Unified.Column5
import Airbender.Proofs.GKRProtocol.ROMColumns.Unified.Column6
import Airbender.Proofs.GKRProtocol.ROMColumns.Unified.Column7
import Airbender.Proofs.GKRProtocol.ROMColumns.Unified.Column8
import Airbender.Proofs.GKRProtocol.ROMColumns.Unified.Column9
import Airbender.Review.Circuits.UnifiedReduced.Tables.Native.ROMData
import Airbender.Proofs.Tables.ZeroTail

namespace Airbender.Compiler.ROMNative.UnifiedValues
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

theorem column0 (index : Fin 1048576) :
    Data.GKRSetup.Unified.setupColumn0.get? (590081 + index.val) = UnifiedReduced.Setup.nativeROMData.columns[0].get? index.val := by
  rw [Airbender.Compiler.ROMColumns.Unified.Column0.column_value index]
  rw [Nat.zero_add]
  rfl

private theorem sourceTail1 : Setup.Proofs.zeroTail 4 Airbender.Compiler.ROMColumns.Unified.Column1.selectedColumn.blocks.toList = true := by decide +kernel

private theorem targetTail1 : Setup.Proofs.zeroTail 4 UnifiedReduced.Setup.nativeROMData.columns[1].blocks.toList = true := by decide +kernel

private theorem targetExtent1 : (UnifiedReduced.Setup.nativeROMData.columns[1].blocks.toList.map Setup.Block.length).sum = 1048576 := by decide +kernel

theorem column1 (index : Fin 1048576) :
    Data.GKRSetup.Unified.setupColumn1.get? (590081 + index.val) = UnifiedReduced.Setup.nativeROMData.columns[1].get? index.val := by
  rw [Airbender.Compiler.ROMColumns.Unified.Column1.column_value index]
  by_cases leading : index.val < 4
  · generalize eq : index.val = n at *
    interval_cases n <;> rfl
  · have sourceValue := Setup.Proofs.zeroTail_sound 4 Airbender.Compiler.ROMColumns.Unified.Column1.selectedColumn.blocks.toList
      sourceTail1 (0 + index.val) (by omega) (by rw [Airbender.Compiler.ROMColumns.Unified.Column1.selectedLength]; have := index.isLt; omega)
    have targetValue := Setup.Proofs.zeroTail_sound 4 UnifiedReduced.Setup.nativeROMData.columns[1].blocks.toList
      targetTail1 index.val (by omega) (by rw [targetExtent1]; exact index.isLt)
    exact sourceValue.trans targetValue.symm

private theorem sourceTail2 : Setup.Proofs.zeroTail 4 Airbender.Compiler.ROMColumns.Unified.Column2.selectedColumn.blocks.toList = true := by decide +kernel

private theorem targetTail2 : Setup.Proofs.zeroTail 4 UnifiedReduced.Setup.nativeROMData.columns[2].blocks.toList = true := by decide +kernel

private theorem targetExtent2 : (UnifiedReduced.Setup.nativeROMData.columns[2].blocks.toList.map Setup.Block.length).sum = 1048576 := by decide +kernel

theorem column2 (index : Fin 1048576) :
    Data.GKRSetup.Unified.setupColumn2.get? (590081 + index.val) = UnifiedReduced.Setup.nativeROMData.columns[2].get? index.val := by
  rw [Airbender.Compiler.ROMColumns.Unified.Column2.column_value index]
  by_cases leading : index.val < 4
  · generalize eq : index.val = n at *
    interval_cases n <;> rfl
  · have sourceValue := Setup.Proofs.zeroTail_sound 4 Airbender.Compiler.ROMColumns.Unified.Column2.selectedColumn.blocks.toList
      sourceTail2 (0 + index.val) (by omega) (by rw [Airbender.Compiler.ROMColumns.Unified.Column2.selectedLength]; have := index.isLt; omega)
    have targetValue := Setup.Proofs.zeroTail_sound 4 UnifiedReduced.Setup.nativeROMData.columns[2].blocks.toList
      targetTail2 index.val (by omega) (by rw [targetExtent2]; exact index.isLt)
    exact sourceValue.trans targetValue.symm

private theorem sourceTail3 : Setup.Proofs.zeroTail 262144 Airbender.Compiler.ROMColumns.Unified.Column3.selectedColumn.blocks.toList = true := by decide +kernel

private theorem targetTail3 : Setup.Proofs.zeroTail 1 UnifiedReduced.Setup.nativeROMData.columns[3].blocks.toList = true := by decide +kernel

private theorem targetExtent3 : (UnifiedReduced.Setup.nativeROMData.columns[3].blocks.toList.map Setup.Block.length).sum = 1048576 := by decide +kernel

theorem column3 (index : Fin 1048576) :
    Data.GKRSetup.Unified.setupColumn3.get? (590081 + index.val) = UnifiedReduced.Setup.nativeROMData.columns[3].get? index.val := by
  rw [Airbender.Compiler.ROMColumns.Unified.Column3.column_value index]
  by_cases leading : index.val < 1
  · generalize eq : index.val = n at *
    interval_cases n; rfl
  · have sourceValue := Setup.Proofs.zeroTail_sound 262144 Airbender.Compiler.ROMColumns.Unified.Column3.selectedColumn.blocks.toList
      sourceTail3 (262143 + index.val) (by omega) (by rw [Airbender.Compiler.ROMColumns.Unified.Column3.selectedLength]; have := index.isLt; omega)
    have targetValue := Setup.Proofs.zeroTail_sound 1 UnifiedReduced.Setup.nativeROMData.columns[3].blocks.toList
      targetTail3 index.val (by omega) (by rw [targetExtent3]; exact index.isLt)
    exact sourceValue.trans targetValue.symm

private theorem sourceTail4 : Setup.Proofs.zeroTail 4 Airbender.Compiler.ROMColumns.Unified.Column4.selectedColumn.blocks.toList = true := by decide +kernel

private theorem targetTail4 : Setup.Proofs.zeroTail 0 UnifiedReduced.Setup.nativeROMData.columns[4].blocks.toList = true := by decide +kernel

private theorem targetExtent4 : (UnifiedReduced.Setup.nativeROMData.columns[4].blocks.toList.map Setup.Block.length).sum = 1048576 := by decide +kernel

theorem column4 (index : Fin 1048576) :
    Data.GKRSetup.Unified.setupColumn4.get? (590081 + index.val) = UnifiedReduced.Setup.nativeROMData.columns[4].get? index.val := by
  rw [Airbender.Compiler.ROMColumns.Unified.Column4.column_value index]
  have sourceValue := Setup.Proofs.zeroTail_sound 4 Airbender.Compiler.ROMColumns.Unified.Column4.selectedColumn.blocks.toList
    sourceTail4 (4 + index.val) (by omega) (by rw [Airbender.Compiler.ROMColumns.Unified.Column4.selectedLength]; have := index.isLt; omega)
  have targetValue := Setup.Proofs.zeroTail_sound 0 UnifiedReduced.Setup.nativeROMData.columns[4].blocks.toList
    targetTail4 index.val (by omega) (by rw [targetExtent4]; exact index.isLt)
  exact sourceValue.trans targetValue.symm

private theorem sourceTail5 : Setup.Proofs.zeroTail 72 Airbender.Compiler.ROMColumns.Unified.Column5.selectedColumn.blocks.toList = true := by decide +kernel

private theorem targetTail5 : Setup.Proofs.zeroTail 3 UnifiedReduced.Setup.nativeROMData.columns[5].blocks.toList = true := by decide +kernel

private theorem targetExtent5 : (UnifiedReduced.Setup.nativeROMData.columns[5].blocks.toList.map Setup.Block.length).sum = 1048576 := by decide +kernel

theorem column5 (index : Fin 1048576) :
    Data.GKRSetup.Unified.setupColumn5.get? (590081 + index.val) = UnifiedReduced.Setup.nativeROMData.columns[5].get? index.val := by
  rw [Airbender.Compiler.ROMColumns.Unified.Column5.column_value index]
  by_cases leading : index.val < 3
  · generalize eq : index.val = n at *
    interval_cases n <;> rfl
  · have sourceValue := Setup.Proofs.zeroTail_sound 72 Airbender.Compiler.ROMColumns.Unified.Column5.selectedColumn.blocks.toList
      sourceTail5 (69 + index.val) (by omega) (by rw [Airbender.Compiler.ROMColumns.Unified.Column5.selectedLength]; have := index.isLt; omega)
    have targetValue := Setup.Proofs.zeroTail_sound 3 UnifiedReduced.Setup.nativeROMData.columns[5].blocks.toList
      targetTail5 index.val (by omega) (by rw [targetExtent5]; exact index.isLt)
    exact sourceValue.trans targetValue.symm

private theorem sourceTail6 : Setup.Proofs.zeroTail 136 Airbender.Compiler.ROMColumns.Unified.Column6.selectedColumn.blocks.toList = true := by decide +kernel

private theorem targetTail6 : Setup.Proofs.zeroTail 3 UnifiedReduced.Setup.nativeROMData.columns[6].blocks.toList = true := by decide +kernel

private theorem targetExtent6 : (UnifiedReduced.Setup.nativeROMData.columns[6].blocks.toList.map Setup.Block.length).sum = 1048576 := by decide +kernel

theorem column6 (index : Fin 1048576) :
    Data.GKRSetup.Unified.setupColumn6.get? (590081 + index.val) = UnifiedReduced.Setup.nativeROMData.columns[6].get? index.val := by
  rw [Airbender.Compiler.ROMColumns.Unified.Column6.column_value index]
  by_cases leading : index.val < 3
  · generalize eq : index.val = n at *
    interval_cases n <;> rfl
  · have sourceValue := Setup.Proofs.zeroTail_sound 136 Airbender.Compiler.ROMColumns.Unified.Column6.selectedColumn.blocks.toList
      sourceTail6 (133 + index.val) (by omega) (by rw [Airbender.Compiler.ROMColumns.Unified.Column6.selectedLength]; have := index.isLt; omega)
    have targetValue := Setup.Proofs.zeroTail_sound 3 UnifiedReduced.Setup.nativeROMData.columns[6].blocks.toList
      targetTail6 index.val (by omega) (by rw [targetExtent6]; exact index.isLt)
    exact sourceValue.trans targetValue.symm

private theorem sourceTail7 : Setup.Proofs.zeroTail 200 Airbender.Compiler.ROMColumns.Unified.Column7.selectedColumn.blocks.toList = true := by decide +kernel

private theorem targetTail7 : Setup.Proofs.zeroTail 3 UnifiedReduced.Setup.nativeROMData.columns[7].blocks.toList = true := by decide +kernel

private theorem targetExtent7 : (UnifiedReduced.Setup.nativeROMData.columns[7].blocks.toList.map Setup.Block.length).sum = 1048576 := by decide +kernel

theorem column7 (index : Fin 1048576) :
    Data.GKRSetup.Unified.setupColumn7.get? (590081 + index.val) = UnifiedReduced.Setup.nativeROMData.columns[7].get? index.val := by
  rw [Airbender.Compiler.ROMColumns.Unified.Column7.column_value index]
  by_cases leading : index.val < 3
  · generalize eq : index.val = n at *
    interval_cases n <;> rfl
  · have sourceValue := Setup.Proofs.zeroTail_sound 200 Airbender.Compiler.ROMColumns.Unified.Column7.selectedColumn.blocks.toList
      sourceTail7 (197 + index.val) (by omega) (by rw [Airbender.Compiler.ROMColumns.Unified.Column7.selectedLength]; have := index.isLt; omega)
    have targetValue := Setup.Proofs.zeroTail_sound 3 UnifiedReduced.Setup.nativeROMData.columns[7].blocks.toList
      targetTail7 index.val (by omega) (by rw [targetExtent7]; exact index.isLt)
    exact sourceValue.trans targetValue.symm

private theorem sourceTail8 : Setup.Proofs.zeroTail 590081 Airbender.Compiler.ROMColumns.Unified.Column8.selectedColumn.blocks.toList = true := by decide +kernel

private theorem targetTail8 : Setup.Proofs.zeroTail 0 UnifiedReduced.Setup.nativeROMData.columns[8].blocks.toList = true := by decide +kernel

private theorem targetExtent8 : (UnifiedReduced.Setup.nativeROMData.columns[8].blocks.toList.map Setup.Block.length).sum = 1048576 := by decide +kernel

theorem column8 (index : Fin 1048576) :
    Data.GKRSetup.Unified.setupColumn8.get? (590081 + index.val) = UnifiedReduced.Setup.nativeROMData.columns[8].get? index.val := by
  rw [Airbender.Compiler.ROMColumns.Unified.Column8.column_value index]
  have sourceValue := Setup.Proofs.zeroTail_sound 590081 Airbender.Compiler.ROMColumns.Unified.Column8.selectedColumn.blocks.toList
    sourceTail8 (590081 + index.val) (by omega) (by rw [Airbender.Compiler.ROMColumns.Unified.Column8.selectedLength]; have := index.isLt; omega)
  have targetValue := Setup.Proofs.zeroTail_sound 0 UnifiedReduced.Setup.nativeROMData.columns[8].blocks.toList
    targetTail8 index.val (by omega) (by rw [targetExtent8]; exact index.isLt)
  exact sourceValue.trans targetValue.symm

theorem column9 (index : Fin 1048576) :
    Data.GKRSetup.Unified.setupColumn9.get? (590081 + index.val) = UnifiedReduced.Setup.nativeROMData.columns[9].get? index.val := by
  rw [Airbender.Compiler.ROMColumns.Unified.Column9.column_value index]
  rw [Nat.zero_add]
  rfl

end Airbender.Compiler.ROMNative.UnifiedValues
