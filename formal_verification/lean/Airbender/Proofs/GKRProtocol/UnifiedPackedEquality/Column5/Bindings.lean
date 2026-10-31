import Airbender.Proofs.GKRProtocol.UnifiedPackedEquality.Column5.Codes
import Airbender.Import.GKRProtocol.BlockCoverageImport

namespace Airbender.Compiler.UnifiedPackedEquality.Column5
open Airbender Airbender.Compiler.PackedSetupEquality
set_option warningAsError true
set_option Elab.async false
-- These views bind both selected spans to the complete native source column.
set_option maxRecDepth 131072
set_option maxHeartbeats 4000000

column_blocks_part rawPrefix from Data.GKRSetup.Unified.setupColumn5 start 0 stop 128
column_blocks_part rawSource0 from Data.GKRSetup.Unified.setupColumn5 start 128 stop 24448
column_blocks_part rawGap from Data.GKRSetup.Unified.setupColumn5 start 24448 stop 24576
column_blocks_part rawSource1 from Data.GKRSetup.Unified.setupColumn5 start 24576 stop 26368
column_blocks_part rawSuffix from Data.GKRSetup.Unified.setupColumn5 start 26368 stop 26494
column_parts_cover sourceLayout from Data.GKRSetup.Unified.setupColumn5
  parts [rawPrefix, rawSource0, rawGap, rawSource1, rawSuffix]

setup_code_binding raw_source0_binding : rawSource0 = source0.map BlockCode.decode
setup_code_binding raw_source1_binding : rawSource1 = source1.map BlockCode.decode

private theorem source_shape : Data.GKRSetup.Unified.setupColumn5.blocks.toList =
    rawPrefix ++ rawSource0 ++ rawGap ++ rawSource1 ++ rawSuffix := by
  simpa only [List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc] using sourceLayout

theorem source0_binding :
    (Data.GKRSetup.Unified.setupColumn5.blocks.toList.drop 128).take 24320 = source0.map BlockCode.decode := by
  apply Eq.trans _ raw_source0_binding
  apply select_middle _ rawPrefix rawSource0 (rawGap ++ rawSource1 ++ rawSuffix) 128 24320
  · simpa only [List.append_assoc] using source_shape
  · decide +kernel
  · decide +kernel

theorem source1_binding :
    (Data.GKRSetup.Unified.setupColumn5.blocks.toList.drop 24576).take 1792 = source1.map BlockCode.decode := by
  apply Eq.trans _ raw_source1_binding
  apply select_middle _ (rawPrefix ++ rawSource0 ++ rawGap) rawSource1 rawSuffix 24576 1792
  · exact source_shape
  · decide +kernel
  · decide +kernel

theorem source_binding :
    (Data.GKRSetup.Unified.setupColumn5.blocks.toList.drop 128).take 24320 ++
    (Data.GKRSetup.Unified.setupColumn5.blocks.toList.drop 24576).take 1792 = sourceCode.map BlockCode.decode := by
  rw [source0_binding, source1_binding]
  simp only [sourceCode, List.map_append]

column_blocks_part rawShiftPrefix from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 0 stop 128
column_blocks_part rawShift from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 128 stop 24448
column_blocks_part rawShiftSuffix from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 24448 stop 24543
column_parts_cover shiftLayout from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) parts [rawShiftPrefix, rawShift, rawShiftSuffix]
setup_code_binding raw_shift_binding : rawShift = shiftCode.map BlockCode.decode

theorem shift_binding :
    ((UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]).blocks.toList.drop 128).take 24320 = shiftCode.map BlockCode.decode := by
  apply Eq.trans _ raw_shift_binding
  apply select_middle _ rawShiftPrefix rawShift rawShiftSuffix 128 24320
  · simpa only [List.flatten_cons, List.flatten_nil, List.append_nil, List.nil_append, List.append_assoc] using shiftLayout
  · decide +kernel
  · decide +kernel

column_blocks_part rawRotate8Prefix from (UnifiedReduced.Setup.nativeRotate8Data.columns[(5 : Nat)]) start 0 stop 16
column_blocks_part rawRotate8 from (UnifiedReduced.Setup.nativeRotate8Data.columns[(5 : Nat)]) start 16 stop 898
column_parts_cover rotate8Layout from (UnifiedReduced.Setup.nativeRotate8Data.columns[(5 : Nat)]) parts [rawRotate8Prefix, rawRotate8]
setup_code_binding raw_rotate8_binding : rawRotate8 = rotate8Code.map BlockCode.decode

theorem rotate8_binding :
    ((UnifiedReduced.Setup.nativeRotate8Data.columns[(5 : Nat)]).blocks.toList.drop 16).take 882 = rotate8Code.map BlockCode.decode := by
  apply Eq.trans _ raw_rotate8_binding
  apply select_middle _ rawRotate8Prefix rawRotate8 [] 16 882
  · simpa only [List.flatten_cons, List.flatten_nil, List.append_nil, List.nil_append, List.append_assoc] using rotate8Layout
  · decide +kernel
  · decide +kernel

column_blocks_part rawRotate7 from (UnifiedReduced.Setup.nativeRotate7Data.columns[(5 : Nat)]) start 0 stop 910
column_blocks_part rawRotate7Suffix from (UnifiedReduced.Setup.nativeRotate7Data.columns[(5 : Nat)]) start 910 stop 1032
column_parts_cover rotate7Layout from (UnifiedReduced.Setup.nativeRotate7Data.columns[(5 : Nat)]) parts [rawRotate7, rawRotate7Suffix]
setup_code_binding raw_rotate7_binding : rawRotate7 = rotate7Code.map BlockCode.decode

theorem rotate7_binding :
    ((UnifiedReduced.Setup.nativeRotate7Data.columns[(5 : Nat)]).blocks.toList.drop 0).take 910 = rotate7Code.map BlockCode.decode := by
  apply Eq.trans _ raw_rotate7_binding
  apply select_middle _ [] rawRotate7 rawRotate7Suffix 0 910
  · simpa only [List.flatten_cons, List.flatten_nil, List.append_nil, List.nil_append, List.append_assoc] using rotate7Layout
  · decide +kernel
  · decide +kernel

theorem target_binding :
    ((UnifiedReduced.Setup.nativeShiftData.columns[5]).blocks.toList.drop 128).take 24320 ++
    ((UnifiedReduced.Setup.nativeRotate8Data.columns[5]).blocks.toList.drop 16).take 882 ++
    ((UnifiedReduced.Setup.nativeRotate7Data.columns[5]).blocks.toList.drop 0).take 910 = targetCode.map BlockCode.decode := by
  rw [shift_binding, rotate8_binding, rotate7_binding]
  simp only [targetCode, List.map_append]


end Airbender.Compiler.UnifiedPackedEquality.Column5
