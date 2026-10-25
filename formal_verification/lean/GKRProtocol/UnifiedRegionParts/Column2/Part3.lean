import GKRProtocol.UnifiedAllPrefix.Column2
import GKRProtocol.SixteenRegions

namespace Airbender.Compiler.UnifiedRegionColumns.Column2
open Airbender Airbender.Compiler Airbender.Compiler.UnifiedAllPrefix.Column2
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

noncomputable def front12 : List Setup.Block := (UnifiedReduced.Setup.nativeZeroData.columns[(2 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeRegisterZeroData.columns[(2 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeCleanupData.columns[(2 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeByteSignData.columns[(2 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeSignData.columns[(2 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeTruncationData.columns[(2 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeShiftData.columns[(2 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeROMData.columns[(2 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeRotate16Data.columns[(2 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeRotate12Data.columns[(2 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeRotate8Data.columns[(2 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeRotate7Data.columns[(2 : Nat)]).blocks.toList
noncomputable def back12 : List Setup.Block := (UnifiedReduced.Setup.nativeXorData.columns[(2 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeOrData.columns[(2 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeAndData.columns[(2 : Nat)]).blocks.toList

theorem regionPrefix12 : (front12.map Setup.Block.length).sum = 1900801 := by
  simp only [front12, List.map_append, List.sum_append, regionLength0, regionLength1, regionLength2, regionLength3, regionLength4, regionLength5, regionLength6, regionLength7, regionLength8, regionLength9, regionLength10, regionLength11]

theorem region_value12 (index : Fin 128) :
    Data.GKRSetup.Unified.setupColumn2.get? (1900801 + index.val) = (UnifiedReduced.Setup.nativeConditionalData.columns[(2 : Nat)]).get? index.val := by
  apply (prefix_value ⟨1900801 + index.val, by have := index.isLt; omega⟩).trans
  have shape : regionBlocks = front12 ++ ((UnifiedReduced.Setup.nativeConditionalData.columns[(2 : Nat)]).blocks.toList ++ back12) := by
    exact sixteen_region_shape12 (UnifiedReduced.Setup.nativeZeroData.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeRegisterZeroData.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeCleanupData.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeByteSignData.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeSignData.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeTruncationData.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeShiftData.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeROMData.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeRotate16Data.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeRotate12Data.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeRotate8Data.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeRotate7Data.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeConditionalData.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeXorData.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeOrData.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeAndData.columns[(2 : Nat)]).blocks.toList
  rw [shape]
  have skipped := Setup.Proofs.skip_blocks front12 ((UnifiedReduced.Setup.nativeConditionalData.columns[(2 : Nat)]).blocks.toList ++ back12) index.val
  rw [regionPrefix12] at skipped
  exact skipped.trans (getFromBlocks_before_suffix _ _ index.val (by rw [regionLength12]; exact index.isLt))

noncomputable def front13 : List Setup.Block := (UnifiedReduced.Setup.nativeZeroData.columns[(2 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeRegisterZeroData.columns[(2 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeCleanupData.columns[(2 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeByteSignData.columns[(2 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeSignData.columns[(2 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeTruncationData.columns[(2 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeShiftData.columns[(2 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeROMData.columns[(2 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeRotate16Data.columns[(2 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeRotate12Data.columns[(2 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeRotate8Data.columns[(2 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeRotate7Data.columns[(2 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeConditionalData.columns[(2 : Nat)]).blocks.toList
noncomputable def back13 : List Setup.Block := (UnifiedReduced.Setup.nativeOrData.columns[(2 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeAndData.columns[(2 : Nat)]).blocks.toList

theorem regionPrefix13 : (front13.map Setup.Block.length).sum = 1900929 := by
  simp only [front13, List.map_append, List.sum_append, regionLength0, regionLength1, regionLength2, regionLength3, regionLength4, regionLength5, regionLength6, regionLength7, regionLength8, regionLength9, regionLength10, regionLength11, regionLength12]

theorem region_value13 (index : Fin 65536) :
    Data.GKRSetup.Unified.setupColumn2.get? (1900929 + index.val) = (UnifiedReduced.Setup.nativeXorData.columns[(2 : Nat)]).get? index.val := by
  apply (prefix_value ⟨1900929 + index.val, by have := index.isLt; omega⟩).trans
  have shape : regionBlocks = front13 ++ ((UnifiedReduced.Setup.nativeXorData.columns[(2 : Nat)]).blocks.toList ++ back13) := by
    exact sixteen_region_shape13 (UnifiedReduced.Setup.nativeZeroData.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeRegisterZeroData.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeCleanupData.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeByteSignData.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeSignData.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeTruncationData.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeShiftData.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeROMData.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeRotate16Data.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeRotate12Data.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeRotate8Data.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeRotate7Data.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeConditionalData.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeXorData.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeOrData.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeAndData.columns[(2 : Nat)]).blocks.toList
  rw [shape]
  have skipped := Setup.Proofs.skip_blocks front13 ((UnifiedReduced.Setup.nativeXorData.columns[(2 : Nat)]).blocks.toList ++ back13) index.val
  rw [regionPrefix13] at skipped
  exact skipped.trans (getFromBlocks_before_suffix _ _ index.val (by rw [regionLength13]; exact index.isLt))

noncomputable def front14 : List Setup.Block := (UnifiedReduced.Setup.nativeZeroData.columns[(2 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeRegisterZeroData.columns[(2 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeCleanupData.columns[(2 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeByteSignData.columns[(2 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeSignData.columns[(2 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeTruncationData.columns[(2 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeShiftData.columns[(2 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeROMData.columns[(2 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeRotate16Data.columns[(2 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeRotate12Data.columns[(2 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeRotate8Data.columns[(2 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeRotate7Data.columns[(2 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeConditionalData.columns[(2 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeXorData.columns[(2 : Nat)]).blocks.toList
noncomputable def back14 : List Setup.Block := (UnifiedReduced.Setup.nativeAndData.columns[(2 : Nat)]).blocks.toList

theorem regionPrefix14 : (front14.map Setup.Block.length).sum = 1966465 := by
  simp only [front14, List.map_append, List.sum_append, regionLength0, regionLength1, regionLength2, regionLength3, regionLength4, regionLength5, regionLength6, regionLength7, regionLength8, regionLength9, regionLength10, regionLength11, regionLength12, regionLength13]

theorem region_value14 (index : Fin 65536) :
    Data.GKRSetup.Unified.setupColumn2.get? (1966465 + index.val) = (UnifiedReduced.Setup.nativeOrData.columns[(2 : Nat)]).get? index.val := by
  apply (prefix_value ⟨1966465 + index.val, by have := index.isLt; omega⟩).trans
  have shape : regionBlocks = front14 ++ ((UnifiedReduced.Setup.nativeOrData.columns[(2 : Nat)]).blocks.toList ++ back14) := by
    exact sixteen_region_shape14 (UnifiedReduced.Setup.nativeZeroData.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeRegisterZeroData.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeCleanupData.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeByteSignData.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeSignData.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeTruncationData.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeShiftData.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeROMData.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeRotate16Data.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeRotate12Data.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeRotate8Data.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeRotate7Data.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeConditionalData.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeXorData.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeOrData.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeAndData.columns[(2 : Nat)]).blocks.toList
  rw [shape]
  have skipped := Setup.Proofs.skip_blocks front14 ((UnifiedReduced.Setup.nativeOrData.columns[(2 : Nat)]).blocks.toList ++ back14) index.val
  rw [regionPrefix14] at skipped
  exact skipped.trans (getFromBlocks_before_suffix _ _ index.val (by rw [regionLength14]; exact index.isLt))

noncomputable def front15 : List Setup.Block := (UnifiedReduced.Setup.nativeZeroData.columns[(2 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeRegisterZeroData.columns[(2 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeCleanupData.columns[(2 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeByteSignData.columns[(2 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeSignData.columns[(2 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeTruncationData.columns[(2 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeShiftData.columns[(2 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeROMData.columns[(2 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeRotate16Data.columns[(2 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeRotate12Data.columns[(2 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeRotate8Data.columns[(2 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeRotate7Data.columns[(2 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeConditionalData.columns[(2 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeXorData.columns[(2 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeOrData.columns[(2 : Nat)]).blocks.toList
noncomputable def back15 : List Setup.Block := []

theorem regionPrefix15 : (front15.map Setup.Block.length).sum = 2032001 := by
  simp only [front15, List.map_append, List.sum_append, regionLength0, regionLength1, regionLength2, regionLength3, regionLength4, regionLength5, regionLength6, regionLength7, regionLength8, regionLength9, regionLength10, regionLength11, regionLength12, regionLength13, regionLength14]

theorem region_value15 (index : Fin 65536) :
    Data.GKRSetup.Unified.setupColumn2.get? (2032001 + index.val) = (UnifiedReduced.Setup.nativeAndData.columns[(2 : Nat)]).get? index.val := by
  apply (prefix_value ⟨2032001 + index.val, by have := index.isLt; omega⟩).trans
  have shape : regionBlocks = front15 ++ ((UnifiedReduced.Setup.nativeAndData.columns[(2 : Nat)]).blocks.toList ++ back15) := by
    exact sixteen_region_shape15 (UnifiedReduced.Setup.nativeZeroData.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeRegisterZeroData.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeCleanupData.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeByteSignData.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeSignData.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeTruncationData.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeShiftData.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeROMData.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeRotate16Data.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeRotate12Data.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeRotate8Data.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeRotate7Data.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeConditionalData.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeXorData.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeOrData.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeAndData.columns[(2 : Nat)]).blocks.toList
  rw [shape]
  have skipped := Setup.Proofs.skip_blocks front15 ((UnifiedReduced.Setup.nativeAndData.columns[(2 : Nat)]).blocks.toList ++ back15) index.val
  rw [regionPrefix15] at skipped
  exact skipped.trans (getFromBlocks_before_suffix _ _ index.val (by rw [regionLength15]; exact index.isLt))

end Airbender.Compiler.UnifiedRegionColumns.Column2
