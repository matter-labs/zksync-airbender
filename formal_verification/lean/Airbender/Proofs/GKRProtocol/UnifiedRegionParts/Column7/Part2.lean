import Airbender.Proofs.GKRProtocol.UnifiedAllPrefix.Column7
import Airbender.Proofs.GKRProtocol.SixteenRegions

namespace Airbender.Compiler.UnifiedRegionColumns.Column7
open Airbender Airbender.Compiler Airbender.Compiler.UnifiedAllPrefix.Column7
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

noncomputable def front8 : List Setup.Block := (UnifiedReduced.Setup.nativeZeroData.columns[(7 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeRegisterZeroData.columns[(7 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeCleanupData.columns[(7 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeByteSignData.columns[(7 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeSignData.columns[(7 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeTruncationData.columns[(7 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeROMData.columns[(7 : Nat)]).blocks.toList
noncomputable def back8 : List Setup.Block := (UnifiedReduced.Setup.nativeRotate12Data.columns[(7 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeRotate8Data.columns[(7 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeRotate7Data.columns[(7 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeConditionalData.columns[(7 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeXorData.columns[(7 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeOrData.columns[(7 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeAndData.columns[(7 : Nat)]).blocks.toList

theorem regionPrefix8 : (front8.map Setup.Block.length).sum = 1638657 := by
  simp only [front8, List.map_append, List.sum_append, regionLength0, regionLength1, regionLength2, regionLength3, regionLength4, regionLength5, regionLength6, regionLength7]

theorem region_value8 (index : Fin 65536) :
    Data.GKRSetup.Unified.setupColumn7.get? (1638657 + index.val) = (UnifiedReduced.Setup.nativeRotate16Data.columns[(7 : Nat)]).get? index.val := by
  apply (prefix_value ⟨1638657 + index.val, by have := index.isLt; omega⟩).trans
  have shape : regionBlocks = front8 ++ ((UnifiedReduced.Setup.nativeRotate16Data.columns[(7 : Nat)]).blocks.toList ++ back8) := by
    exact sixteen_region_shape8 (UnifiedReduced.Setup.nativeZeroData.columns[(7 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeRegisterZeroData.columns[(7 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeCleanupData.columns[(7 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeByteSignData.columns[(7 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeSignData.columns[(7 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeTruncationData.columns[(7 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeROMData.columns[(7 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeRotate16Data.columns[(7 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeRotate12Data.columns[(7 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeRotate8Data.columns[(7 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeRotate7Data.columns[(7 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeConditionalData.columns[(7 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeXorData.columns[(7 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeOrData.columns[(7 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeAndData.columns[(7 : Nat)]).blocks.toList
  rw [shape]
  have skipped := Setup.Proofs.skip_blocks front8 ((UnifiedReduced.Setup.nativeRotate16Data.columns[(7 : Nat)]).blocks.toList ++ back8) index.val
  rw [regionPrefix8] at skipped
  exact skipped.trans (getFromBlocks_before_suffix _ _ index.val (by rw [regionLength8]; exact index.isLt))

noncomputable def front9 : List Setup.Block := (UnifiedReduced.Setup.nativeZeroData.columns[(7 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeRegisterZeroData.columns[(7 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeCleanupData.columns[(7 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeByteSignData.columns[(7 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeSignData.columns[(7 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeTruncationData.columns[(7 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeROMData.columns[(7 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeRotate16Data.columns[(7 : Nat)]).blocks.toList
noncomputable def back9 : List Setup.Block := (UnifiedReduced.Setup.nativeRotate8Data.columns[(7 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeRotate7Data.columns[(7 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeConditionalData.columns[(7 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeXorData.columns[(7 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeOrData.columns[(7 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeAndData.columns[(7 : Nat)]).blocks.toList

theorem regionPrefix9 : (front9.map Setup.Block.length).sum = 1704193 := by
  simp only [front9, List.map_append, List.sum_append, regionLength0, regionLength1, regionLength2, regionLength3, regionLength4, regionLength5, regionLength6, regionLength7, regionLength8]

theorem region_value9 (index : Fin 65536) :
    Data.GKRSetup.Unified.setupColumn7.get? (1704193 + index.val) = (UnifiedReduced.Setup.nativeRotate12Data.columns[(7 : Nat)]).get? index.val := by
  apply (prefix_value ⟨1704193 + index.val, by have := index.isLt; omega⟩).trans
  have shape : regionBlocks = front9 ++ ((UnifiedReduced.Setup.nativeRotate12Data.columns[(7 : Nat)]).blocks.toList ++ back9) := by
    exact sixteen_region_shape9 (UnifiedReduced.Setup.nativeZeroData.columns[(7 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeRegisterZeroData.columns[(7 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeCleanupData.columns[(7 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeByteSignData.columns[(7 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeSignData.columns[(7 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeTruncationData.columns[(7 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeROMData.columns[(7 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeRotate16Data.columns[(7 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeRotate12Data.columns[(7 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeRotate8Data.columns[(7 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeRotate7Data.columns[(7 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeConditionalData.columns[(7 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeXorData.columns[(7 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeOrData.columns[(7 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeAndData.columns[(7 : Nat)]).blocks.toList
  rw [shape]
  have skipped := Setup.Proofs.skip_blocks front9 ((UnifiedReduced.Setup.nativeRotate12Data.columns[(7 : Nat)]).blocks.toList ++ back9) index.val
  rw [regionPrefix9] at skipped
  exact skipped.trans (getFromBlocks_before_suffix _ _ index.val (by rw [regionLength9]; exact index.isLt))

noncomputable def front10 : List Setup.Block := (UnifiedReduced.Setup.nativeZeroData.columns[(7 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeRegisterZeroData.columns[(7 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeCleanupData.columns[(7 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeByteSignData.columns[(7 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeSignData.columns[(7 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeTruncationData.columns[(7 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeROMData.columns[(7 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeRotate16Data.columns[(7 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeRotate12Data.columns[(7 : Nat)]).blocks.toList
noncomputable def back10 : List Setup.Block := (UnifiedReduced.Setup.nativeRotate7Data.columns[(7 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeConditionalData.columns[(7 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeXorData.columns[(7 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeOrData.columns[(7 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeAndData.columns[(7 : Nat)]).blocks.toList

theorem regionPrefix10 : (front10.map Setup.Block.length).sum = 1769729 := by
  simp only [front10, List.map_append, List.sum_append, regionLength0, regionLength1, regionLength2, regionLength3, regionLength4, regionLength5, regionLength6, regionLength7, regionLength8, regionLength9]

theorem region_value10 (index : Fin 65536) :
    Data.GKRSetup.Unified.setupColumn7.get? (1769729 + index.val) = (UnifiedReduced.Setup.nativeRotate8Data.columns[(7 : Nat)]).get? index.val := by
  apply (prefix_value ⟨1769729 + index.val, by have := index.isLt; omega⟩).trans
  have shape : regionBlocks = front10 ++ ((UnifiedReduced.Setup.nativeRotate8Data.columns[(7 : Nat)]).blocks.toList ++ back10) := by
    exact sixteen_region_shape10 (UnifiedReduced.Setup.nativeZeroData.columns[(7 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeRegisterZeroData.columns[(7 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeCleanupData.columns[(7 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeByteSignData.columns[(7 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeSignData.columns[(7 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeTruncationData.columns[(7 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeROMData.columns[(7 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeRotate16Data.columns[(7 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeRotate12Data.columns[(7 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeRotate8Data.columns[(7 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeRotate7Data.columns[(7 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeConditionalData.columns[(7 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeXorData.columns[(7 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeOrData.columns[(7 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeAndData.columns[(7 : Nat)]).blocks.toList
  rw [shape]
  have skipped := Setup.Proofs.skip_blocks front10 ((UnifiedReduced.Setup.nativeRotate8Data.columns[(7 : Nat)]).blocks.toList ++ back10) index.val
  rw [regionPrefix10] at skipped
  exact skipped.trans (getFromBlocks_before_suffix _ _ index.val (by rw [regionLength10]; exact index.isLt))

noncomputable def front11 : List Setup.Block := (UnifiedReduced.Setup.nativeZeroData.columns[(7 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeRegisterZeroData.columns[(7 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeCleanupData.columns[(7 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeByteSignData.columns[(7 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeSignData.columns[(7 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeTruncationData.columns[(7 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeROMData.columns[(7 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeRotate16Data.columns[(7 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeRotate12Data.columns[(7 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeRotate8Data.columns[(7 : Nat)]).blocks.toList
noncomputable def back11 : List Setup.Block := (UnifiedReduced.Setup.nativeConditionalData.columns[(7 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeXorData.columns[(7 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeOrData.columns[(7 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeAndData.columns[(7 : Nat)]).blocks.toList

theorem regionPrefix11 : (front11.map Setup.Block.length).sum = 1835265 := by
  simp only [front11, List.map_append, List.sum_append, regionLength0, regionLength1, regionLength2, regionLength3, regionLength4, regionLength5, regionLength6, regionLength7, regionLength8, regionLength9, regionLength10]

theorem region_value11 (index : Fin 65536) :
    Data.GKRSetup.Unified.setupColumn7.get? (1835265 + index.val) = (UnifiedReduced.Setup.nativeRotate7Data.columns[(7 : Nat)]).get? index.val := by
  apply (prefix_value ⟨1835265 + index.val, by have := index.isLt; omega⟩).trans
  have shape : regionBlocks = front11 ++ ((UnifiedReduced.Setup.nativeRotate7Data.columns[(7 : Nat)]).blocks.toList ++ back11) := by
    exact sixteen_region_shape11 (UnifiedReduced.Setup.nativeZeroData.columns[(7 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeRegisterZeroData.columns[(7 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeCleanupData.columns[(7 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeByteSignData.columns[(7 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeSignData.columns[(7 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeTruncationData.columns[(7 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeROMData.columns[(7 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeRotate16Data.columns[(7 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeRotate12Data.columns[(7 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeRotate8Data.columns[(7 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeRotate7Data.columns[(7 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeConditionalData.columns[(7 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeXorData.columns[(7 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeOrData.columns[(7 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeAndData.columns[(7 : Nat)]).blocks.toList
  rw [shape]
  have skipped := Setup.Proofs.skip_blocks front11 ((UnifiedReduced.Setup.nativeRotate7Data.columns[(7 : Nat)]).blocks.toList ++ back11) index.val
  rw [regionPrefix11] at skipped
  exact skipped.trans (getFromBlocks_before_suffix _ _ index.val (by rw [regionLength11]; exact index.isLt))

end Airbender.Compiler.UnifiedRegionColumns.Column7
