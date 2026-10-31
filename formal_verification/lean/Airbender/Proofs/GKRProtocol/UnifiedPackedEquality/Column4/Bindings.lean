import Airbender.Proofs.GKRProtocol.UnifiedPackedEquality.Column4.Codes
import Airbender.Import.GKRProtocol.BlockCoverageImport

namespace Airbender.Compiler.UnifiedPackedEquality.Column4
open Airbender Airbender.Compiler.PackedSetupEquality
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
-- Bind the complete fixed spans to the native columns.
set_option maxHeartbeats 4000000

column_blocks_part rawPrefix from Data.GKRSetup.Unified.setupColumn4 start 0 stop 128
column_blocks_part rawSource0 from Data.GKRSetup.Unified.setupColumn4 start 128 stop 24320
column_blocks_part rawGap1 from Data.GKRSetup.Unified.setupColumn4 start 24320 stop 24448
column_blocks_part rawSource1 from Data.GKRSetup.Unified.setupColumn4 start 24448 stop 25472
column_blocks_part rawSuffix from Data.GKRSetup.Unified.setupColumn4 start 25472 stop 25573
column_parts_cover sourceLayout from Data.GKRSetup.Unified.setupColumn4 parts [rawPrefix, rawSource0, rawGap1, rawSource1, rawSuffix]

setup_code_binding raw_source0_binding : rawSource0 = source0.map BlockCode.decode
setup_code_binding raw_source1_binding : rawSource1 = source1.map BlockCode.decode

private theorem source_shape : Data.GKRSetup.Unified.setupColumn4.blocks.toList = rawPrefix ++ rawSource0 ++ rawGap1 ++ rawSource1 ++ rawSuffix := by
  simpa only [List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc] using sourceLayout

theorem source0_binding : (Data.GKRSetup.Unified.setupColumn4.blocks.toList.drop 128).take 24192 = source0.map BlockCode.decode := by
  apply Eq.trans _ raw_source0_binding
  apply select_middle _ (rawPrefix) rawSource0 (rawGap1 ++ rawSource1 ++ rawSuffix) 128 24192
  · simpa only [List.append_assoc] using source_shape
  · decide +kernel
  · decide +kernel

theorem source1_binding : (Data.GKRSetup.Unified.setupColumn4.blocks.toList.drop 24448).take 1024 = source1.map BlockCode.decode := by
  apply Eq.trans _ raw_source1_binding
  apply select_middle _ (rawPrefix ++ rawSource0 ++ rawGap1) rawSource1 (rawSuffix) 24448 1024
  · simpa only [List.append_assoc] using source_shape
  · decide +kernel
  · decide +kernel

theorem source_binding : (Data.GKRSetup.Unified.setupColumn4.blocks.toList.drop 128).take 24192 ++ (Data.GKRSetup.Unified.setupColumn4.blocks.toList.drop 24448).take 1024 = sourceCode.map BlockCode.decode := by
  rw [source0_binding, source1_binding]
  simp only [sourceCode, List.map_append]

column_blocks_part rawShiftPrefix from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 0 stop 128
column_blocks_part rawShift from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 128 stop 24320
column_blocks_part rawShiftSuffix from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 24320 stop 24415
column_parts_cover shiftLayout from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) parts [rawShiftPrefix, rawShift, rawShiftSuffix]
setup_code_binding raw_shift_binding : rawShift = shiftCode.map BlockCode.decode

theorem shift_binding : ((UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]).blocks.toList.drop 128).take 24192 = shiftCode.map BlockCode.decode := by
  apply Eq.trans _ raw_shift_binding
  apply select_middle _ rawShiftPrefix rawShift rawShiftSuffix 128 24192
  · simpa only [List.flatten_cons, List.flatten_nil, List.append_nil, List.nil_append, List.append_assoc] using shiftLayout
  · decide +kernel
  · decide +kernel

column_blocks_part rawRotate16Prefix from (UnifiedReduced.Setup.nativeRotate16Data.columns[(4 : Nat)]) start 0 stop 34
column_blocks_part rawRotate16 from (UnifiedReduced.Setup.nativeRotate16Data.columns[(4 : Nat)]) start 34 stop 899
column_parts_cover rotate16Layout from (UnifiedReduced.Setup.nativeRotate16Data.columns[(4 : Nat)]) parts [rawRotate16Prefix, rawRotate16]
setup_code_binding raw_rotate16_binding : rawRotate16 = rotate16Code.map BlockCode.decode

theorem rotate16_binding : ((UnifiedReduced.Setup.nativeRotate16Data.columns[(4 : Nat)]).blocks.toList.drop 34).take 865 = rotate16Code.map BlockCode.decode := by
  apply Eq.trans _ raw_rotate16_binding
  apply select_middle _ rawRotate16Prefix rawRotate16 [] 34 865
  · simpa only [List.flatten_cons, List.flatten_nil, List.append_nil, List.nil_append, List.append_assoc] using rotate16Layout
  · decide +kernel
  · decide +kernel

column_blocks_part rawRotate12 from (UnifiedReduced.Setup.nativeRotate12Data.columns[(4 : Nat)]) start 0 stop 159
column_blocks_part rawRotate12Suffix from (UnifiedReduced.Setup.nativeRotate12Data.columns[(4 : Nat)]) start 159 stop 256
column_parts_cover rotate12Layout from (UnifiedReduced.Setup.nativeRotate12Data.columns[(4 : Nat)]) parts [rawRotate12, rawRotate12Suffix]
setup_code_binding raw_rotate12_binding : rawRotate12 = rotate12Code.map BlockCode.decode

theorem rotate12_binding : ((UnifiedReduced.Setup.nativeRotate12Data.columns[(4 : Nat)]).blocks.toList.drop 0).take 159 = rotate12Code.map BlockCode.decode := by
  apply Eq.trans _ raw_rotate12_binding
  apply select_middle _ [] rawRotate12 rawRotate12Suffix 0 159
  · simpa only [List.flatten_cons, List.flatten_nil, List.append_nil, List.nil_append, List.append_assoc] using rotate12Layout
  · decide +kernel
  · decide +kernel

theorem target_binding : ((UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]).blocks.toList.drop 128).take 24192 ++ ((UnifiedReduced.Setup.nativeRotate16Data.columns[(4 : Nat)]).blocks.toList.drop 34).take 865 ++ ((UnifiedReduced.Setup.nativeRotate12Data.columns[(4 : Nat)]).blocks.toList.drop 0).take 159 = targetCode.map BlockCode.decode := by
  rw [shift_binding, rotate16_binding, rotate12_binding]
  simp only [targetCode, List.map_append]

end Airbender.Compiler.UnifiedPackedEquality.Column4
