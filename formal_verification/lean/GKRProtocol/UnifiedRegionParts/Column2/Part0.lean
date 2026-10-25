import GKRProtocol.UnifiedAllPrefix.Column2
import GKRProtocol.SixteenRegions

namespace Airbender.Compiler.UnifiedRegionColumns.Column2
open Airbender Airbender.Compiler Airbender.Compiler.UnifiedAllPrefix.Column2
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

noncomputable def front0 : List Setup.Block := []
noncomputable def back0 : List Setup.Block := (UnifiedReduced.Setup.nativeRegisterZeroData.columns[(2 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeCleanupData.columns[(2 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeByteSignData.columns[(2 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeSignData.columns[(2 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeTruncationData.columns[(2 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeShiftData.columns[(2 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeROMData.columns[(2 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeRotate16Data.columns[(2 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeRotate12Data.columns[(2 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeRotate8Data.columns[(2 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeRotate7Data.columns[(2 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeConditionalData.columns[(2 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeXorData.columns[(2 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeOrData.columns[(2 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeAndData.columns[(2 : Nat)]).blocks.toList

theorem regionPrefix0 : (front0.map Setup.Block.length).sum = 0 := by
  rfl

theorem region_value0 (index : Fin 1) :
    Data.GKRSetup.Unified.setupColumn2.get? (0 + index.val) = (UnifiedReduced.Setup.nativeZeroData.columns[(2 : Nat)]).get? index.val := by
  apply (prefix_value ⟨0 + index.val, by have := index.isLt; omega⟩).trans
  have shape : regionBlocks = front0 ++ ((UnifiedReduced.Setup.nativeZeroData.columns[(2 : Nat)]).blocks.toList ++ back0) := by
    exact sixteen_region_shape0 (UnifiedReduced.Setup.nativeZeroData.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeRegisterZeroData.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeCleanupData.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeByteSignData.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeSignData.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeTruncationData.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeShiftData.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeROMData.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeRotate16Data.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeRotate12Data.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeRotate8Data.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeRotate7Data.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeConditionalData.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeXorData.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeOrData.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeAndData.columns[(2 : Nat)]).blocks.toList
  rw [shape]
  have skipped := Setup.Proofs.skip_blocks front0 ((UnifiedReduced.Setup.nativeZeroData.columns[(2 : Nat)]).blocks.toList ++ back0) index.val
  rw [regionPrefix0] at skipped
  exact skipped.trans (getFromBlocks_before_suffix _ _ index.val (by rw [regionLength0]; exact index.isLt))

noncomputable def front1 : List Setup.Block := (UnifiedReduced.Setup.nativeZeroData.columns[(2 : Nat)]).blocks.toList
noncomputable def back1 : List Setup.Block := (UnifiedReduced.Setup.nativeCleanupData.columns[(2 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeByteSignData.columns[(2 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeSignData.columns[(2 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeTruncationData.columns[(2 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeShiftData.columns[(2 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeROMData.columns[(2 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeRotate16Data.columns[(2 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeRotate12Data.columns[(2 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeRotate8Data.columns[(2 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeRotate7Data.columns[(2 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeConditionalData.columns[(2 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeXorData.columns[(2 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeOrData.columns[(2 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeAndData.columns[(2 : Nat)]).blocks.toList

theorem regionPrefix1 : (front1.map Setup.Block.length).sum = 1 := by
  exact regionLength0

theorem region_value1 (index : Fin 131072) :
    Data.GKRSetup.Unified.setupColumn2.get? (1 + index.val) = (UnifiedReduced.Setup.nativeRegisterZeroData.columns[(2 : Nat)]).get? index.val := by
  apply (prefix_value ⟨1 + index.val, by have := index.isLt; omega⟩).trans
  have shape : regionBlocks = front1 ++ ((UnifiedReduced.Setup.nativeRegisterZeroData.columns[(2 : Nat)]).blocks.toList ++ back1) := by
    exact sixteen_region_shape1 (UnifiedReduced.Setup.nativeZeroData.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeRegisterZeroData.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeCleanupData.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeByteSignData.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeSignData.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeTruncationData.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeShiftData.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeROMData.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeRotate16Data.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeRotate12Data.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeRotate8Data.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeRotate7Data.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeConditionalData.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeXorData.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeOrData.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeAndData.columns[(2 : Nat)]).blocks.toList
  rw [shape]
  have skipped := Setup.Proofs.skip_blocks front1 ((UnifiedReduced.Setup.nativeRegisterZeroData.columns[(2 : Nat)]).blocks.toList ++ back1) index.val
  rw [regionPrefix1] at skipped
  exact skipped.trans (getFromBlocks_before_suffix _ _ index.val (by rw [regionLength1]; exact index.isLt))

noncomputable def front2 : List Setup.Block := (UnifiedReduced.Setup.nativeZeroData.columns[(2 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeRegisterZeroData.columns[(2 : Nat)]).blocks.toList
noncomputable def back2 : List Setup.Block := (UnifiedReduced.Setup.nativeByteSignData.columns[(2 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeSignData.columns[(2 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeTruncationData.columns[(2 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeShiftData.columns[(2 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeROMData.columns[(2 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeRotate16Data.columns[(2 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeRotate12Data.columns[(2 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeRotate8Data.columns[(2 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeRotate7Data.columns[(2 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeConditionalData.columns[(2 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeXorData.columns[(2 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeOrData.columns[(2 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeAndData.columns[(2 : Nat)]).blocks.toList

theorem regionPrefix2 : (front2.map Setup.Block.length).sum = 131073 := by
  simp only [front2, List.map_append, List.sum_append, regionLength0, regionLength1]

theorem region_value2 (index : Fin 65536) :
    Data.GKRSetup.Unified.setupColumn2.get? (131073 + index.val) = (UnifiedReduced.Setup.nativeCleanupData.columns[(2 : Nat)]).get? index.val := by
  apply (prefix_value ⟨131073 + index.val, by have := index.isLt; omega⟩).trans
  have shape : regionBlocks = front2 ++ ((UnifiedReduced.Setup.nativeCleanupData.columns[(2 : Nat)]).blocks.toList ++ back2) := by
    exact sixteen_region_shape2 (UnifiedReduced.Setup.nativeZeroData.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeRegisterZeroData.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeCleanupData.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeByteSignData.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeSignData.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeTruncationData.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeShiftData.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeROMData.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeRotate16Data.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeRotate12Data.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeRotate8Data.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeRotate7Data.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeConditionalData.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeXorData.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeOrData.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeAndData.columns[(2 : Nat)]).blocks.toList
  rw [shape]
  have skipped := Setup.Proofs.skip_blocks front2 ((UnifiedReduced.Setup.nativeCleanupData.columns[(2 : Nat)]).blocks.toList ++ back2) index.val
  rw [regionPrefix2] at skipped
  exact skipped.trans (getFromBlocks_before_suffix _ _ index.val (by rw [regionLength2]; exact index.isLt))

noncomputable def front3 : List Setup.Block := (UnifiedReduced.Setup.nativeZeroData.columns[(2 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeRegisterZeroData.columns[(2 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeCleanupData.columns[(2 : Nat)]).blocks.toList
noncomputable def back3 : List Setup.Block := (UnifiedReduced.Setup.nativeSignData.columns[(2 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeTruncationData.columns[(2 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeShiftData.columns[(2 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeROMData.columns[(2 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeRotate16Data.columns[(2 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeRotate12Data.columns[(2 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeRotate8Data.columns[(2 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeRotate7Data.columns[(2 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeConditionalData.columns[(2 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeXorData.columns[(2 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeOrData.columns[(2 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeAndData.columns[(2 : Nat)]).blocks.toList

theorem regionPrefix3 : (front3.map Setup.Block.length).sum = 196609 := by
  simp only [front3, List.map_append, List.sum_append, regionLength0, regionLength1, regionLength2]

theorem region_value3 (index : Fin 256) :
    Data.GKRSetup.Unified.setupColumn2.get? (196609 + index.val) = (UnifiedReduced.Setup.nativeByteSignData.columns[(2 : Nat)]).get? index.val := by
  apply (prefix_value ⟨196609 + index.val, by have := index.isLt; omega⟩).trans
  have shape : regionBlocks = front3 ++ ((UnifiedReduced.Setup.nativeByteSignData.columns[(2 : Nat)]).blocks.toList ++ back3) := by
    exact sixteen_region_shape3 (UnifiedReduced.Setup.nativeZeroData.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeRegisterZeroData.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeCleanupData.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeByteSignData.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeSignData.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeTruncationData.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeShiftData.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeROMData.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeRotate16Data.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeRotate12Data.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeRotate8Data.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeRotate7Data.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeConditionalData.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeXorData.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeOrData.columns[(2 : Nat)]).blocks.toList (UnifiedReduced.Setup.nativeAndData.columns[(2 : Nat)]).blocks.toList
  rw [shape]
  have skipped := Setup.Proofs.skip_blocks front3 ((UnifiedReduced.Setup.nativeByteSignData.columns[(2 : Nat)]).blocks.toList ++ back3) index.val
  rw [regionPrefix3] at skipped
  exact skipped.trans (getFromBlocks_before_suffix _ _ index.val (by rw [regionLength3]; exact index.isLt))

end Airbender.Compiler.UnifiedRegionColumns.Column2
