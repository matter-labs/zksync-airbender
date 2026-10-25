import GKRProtocol.UnifiedPrefixNative.Column1
import GKRProtocol.SixteenRegions

namespace Airbender.Compiler.UnifiedRegionColumns.Column1
open Airbender Airbender.Compiler Airbender.Compiler.UnifiedPrefixNative.Column1
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

noncomputable def front4 : List Setup.Block := (UnifiedReduced.Setup.nativeZeroData.columns[(1 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeRegisterZeroData.columns[(1 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeCleanupData.columns[(1 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeByteSignData.columns[(1 : Nat)]).blocks.toList
noncomputable def back4 : List Setup.Block := (UnifiedReduced.Setup.nativeTruncationData.columns[(1 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeShiftData.columns[(1 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeROMData.columns[(1 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeRotate16Data.columns[(1 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeRotate12Data.columns[(1 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeRotate8Data.columns[(1 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeRotate7Data.columns[(1 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeConditionalData.columns[(1 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeXorData.columns[(1 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeOrData.columns[(1 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeAndData.columns[(1 : Nat)]).blocks.toList

theorem regionPrefix4 : (front4.map Setup.Block.length).sum = 196865 := by
  simp only [front4, List.map_append, List.sum_append, regionLength0, regionLength1, regionLength2, regionLength3]

theorem region_value4 (index : Fin 65536) :
    Data.GKRSetup.Unified.setupColumn1.get? (196865 + index.val) = (UnifiedReduced.Setup.nativeSignData.columns[(1 : Nat)]).get? index.val := by
  apply (prefix_value ⟨196865 + index.val, by have := index.isLt; omega⟩).trans
  have shape : regionBlocks = front4 ++ ((UnifiedReduced.Setup.nativeSignData.columns[(1 : Nat)]).blocks.toList ++ back4) := by
    exact sixteen_region_shape4 (UnifiedReduced.Setup.nativeZeroData.columns[(1 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeRegisterZeroData.columns[(1 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeCleanupData.columns[(1 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeByteSignData.columns[(1 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeSignData.columns[(1 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeTruncationData.columns[(1 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeShiftData.columns[(1 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeROMData.columns[(1 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeRotate16Data.columns[(1 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeRotate12Data.columns[(1 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeRotate8Data.columns[(1 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeRotate7Data.columns[(1 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeConditionalData.columns[(1 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeXorData.columns[(1 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeOrData.columns[(1 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeAndData.columns[(1 : Nat)]).blocks.toList
  rw [shape]
  have skipped := Setup.Proofs.skip_blocks front4 ((UnifiedReduced.Setup.nativeSignData.columns[(1 : Nat)]).blocks.toList ++ back4) index.val
  rw [regionPrefix4] at skipped
  exact skipped.trans (getFromBlocks_before_suffix _ _ index.val (by rw [regionLength4]; exact index.isLt))

noncomputable def front5 : List Setup.Block := (UnifiedReduced.Setup.nativeZeroData.columns[(1 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeRegisterZeroData.columns[(1 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeCleanupData.columns[(1 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeByteSignData.columns[(1 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeSignData.columns[(1 : Nat)]).blocks.toList
noncomputable def back5 : List Setup.Block := (UnifiedReduced.Setup.nativeShiftData.columns[(1 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeROMData.columns[(1 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeRotate16Data.columns[(1 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeRotate12Data.columns[(1 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeRotate8Data.columns[(1 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeRotate7Data.columns[(1 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeConditionalData.columns[(1 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeXorData.columns[(1 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeOrData.columns[(1 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeAndData.columns[(1 : Nat)]).blocks.toList

theorem regionPrefix5 : (front5.map Setup.Block.length).sum = 262401 := by
  simp only [front5, List.map_append, List.sum_append, regionLength0, regionLength1, regionLength2, regionLength3, regionLength4]

theorem region_value5 (index : Fin 65536) :
    Data.GKRSetup.Unified.setupColumn1.get? (262401 + index.val) = (UnifiedReduced.Setup.nativeTruncationData.columns[(1 : Nat)]).get? index.val := by
  apply (prefix_value ⟨262401 + index.val, by have := index.isLt; omega⟩).trans
  have shape : regionBlocks = front5 ++ ((UnifiedReduced.Setup.nativeTruncationData.columns[(1 : Nat)]).blocks.toList ++ back5) := by
    exact sixteen_region_shape5 (UnifiedReduced.Setup.nativeZeroData.columns[(1 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeRegisterZeroData.columns[(1 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeCleanupData.columns[(1 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeByteSignData.columns[(1 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeSignData.columns[(1 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeTruncationData.columns[(1 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeShiftData.columns[(1 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeROMData.columns[(1 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeRotate16Data.columns[(1 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeRotate12Data.columns[(1 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeRotate8Data.columns[(1 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeRotate7Data.columns[(1 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeConditionalData.columns[(1 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeXorData.columns[(1 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeOrData.columns[(1 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeAndData.columns[(1 : Nat)]).blocks.toList
  rw [shape]
  have skipped := Setup.Proofs.skip_blocks front5 ((UnifiedReduced.Setup.nativeTruncationData.columns[(1 : Nat)]).blocks.toList ++ back5) index.val
  rw [regionPrefix5] at skipped
  exact skipped.trans (getFromBlocks_before_suffix _ _ index.val (by rw [regionLength5]; exact index.isLt))

noncomputable def front6 : List Setup.Block := (UnifiedReduced.Setup.nativeZeroData.columns[(1 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeRegisterZeroData.columns[(1 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeCleanupData.columns[(1 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeByteSignData.columns[(1 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeSignData.columns[(1 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeTruncationData.columns[(1 : Nat)]).blocks.toList
noncomputable def back6 : List Setup.Block := (UnifiedReduced.Setup.nativeROMData.columns[(1 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeRotate16Data.columns[(1 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeRotate12Data.columns[(1 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeRotate8Data.columns[(1 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeRotate7Data.columns[(1 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeConditionalData.columns[(1 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeXorData.columns[(1 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeOrData.columns[(1 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeAndData.columns[(1 : Nat)]).blocks.toList

theorem regionPrefix6 : (front6.map Setup.Block.length).sum = 327937 := by
  simp only [front6, List.map_append, List.sum_append, regionLength0, regionLength1, regionLength2, regionLength3, regionLength4, regionLength5]

theorem region_value6 (index : Fin 262144) :
    Data.GKRSetup.Unified.setupColumn1.get? (327937 + index.val) = (UnifiedReduced.Setup.nativeShiftData.columns[(1 : Nat)]).get? index.val := by
  apply (prefix_value ⟨327937 + index.val, by have := index.isLt; omega⟩).trans
  have shape : regionBlocks = front6 ++ ((UnifiedReduced.Setup.nativeShiftData.columns[(1 : Nat)]).blocks.toList ++ back6) := by
    exact sixteen_region_shape6 (UnifiedReduced.Setup.nativeZeroData.columns[(1 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeRegisterZeroData.columns[(1 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeCleanupData.columns[(1 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeByteSignData.columns[(1 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeSignData.columns[(1 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeTruncationData.columns[(1 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeShiftData.columns[(1 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeROMData.columns[(1 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeRotate16Data.columns[(1 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeRotate12Data.columns[(1 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeRotate8Data.columns[(1 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeRotate7Data.columns[(1 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeConditionalData.columns[(1 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeXorData.columns[(1 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeOrData.columns[(1 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeAndData.columns[(1 : Nat)]).blocks.toList
  rw [shape]
  have skipped := Setup.Proofs.skip_blocks front6 ((UnifiedReduced.Setup.nativeShiftData.columns[(1 : Nat)]).blocks.toList ++ back6) index.val
  rw [regionPrefix6] at skipped
  exact skipped.trans (getFromBlocks_before_suffix _ _ index.val (by rw [regionLength6]; exact index.isLt))

noncomputable def front7 : List Setup.Block := (UnifiedReduced.Setup.nativeZeroData.columns[(1 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeRegisterZeroData.columns[(1 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeCleanupData.columns[(1 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeByteSignData.columns[(1 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeSignData.columns[(1 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeTruncationData.columns[(1 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeShiftData.columns[(1 : Nat)]).blocks.toList
noncomputable def back7 : List Setup.Block := (UnifiedReduced.Setup.nativeRotate16Data.columns[(1 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeRotate12Data.columns[(1 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeRotate8Data.columns[(1 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeRotate7Data.columns[(1 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeConditionalData.columns[(1 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeXorData.columns[(1 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeOrData.columns[(1 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeAndData.columns[(1 : Nat)]).blocks.toList

theorem regionPrefix7 : (front7.map Setup.Block.length).sum = 590081 := by
  simp only [front7, List.map_append, List.sum_append, regionLength0, regionLength1, regionLength2, regionLength3, regionLength4, regionLength5, regionLength6]

theorem region_value7 (index : Fin 1048576) :
    Data.GKRSetup.Unified.setupColumn1.get? (590081 + index.val) = (UnifiedReduced.Setup.nativeROMData.columns[(1 : Nat)]).get? index.val := by
  apply (prefix_value ⟨590081 + index.val, by have := index.isLt; omega⟩).trans
  have shape : regionBlocks = front7 ++ ((UnifiedReduced.Setup.nativeROMData.columns[(1 : Nat)]).blocks.toList ++ back7) := by
    exact sixteen_region_shape7 (UnifiedReduced.Setup.nativeZeroData.columns[(1 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeRegisterZeroData.columns[(1 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeCleanupData.columns[(1 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeByteSignData.columns[(1 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeSignData.columns[(1 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeTruncationData.columns[(1 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeShiftData.columns[(1 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeROMData.columns[(1 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeRotate16Data.columns[(1 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeRotate12Data.columns[(1 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeRotate8Data.columns[(1 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeRotate7Data.columns[(1 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeConditionalData.columns[(1 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeXorData.columns[(1 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeOrData.columns[(1 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeAndData.columns[(1 : Nat)]).blocks.toList
  rw [shape]
  have skipped := Setup.Proofs.skip_blocks front7 ((UnifiedReduced.Setup.nativeROMData.columns[(1 : Nat)]).blocks.toList ++ back7) index.val
  rw [regionPrefix7] at skipped
  exact skipped.trans (getFromBlocks_before_suffix _ _ index.val (by rw [regionLength7]; exact index.isLt))

end Airbender.Compiler.UnifiedRegionColumns.Column1
