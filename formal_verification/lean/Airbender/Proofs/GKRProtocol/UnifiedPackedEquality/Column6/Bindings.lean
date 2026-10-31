import Airbender.Proofs.GKRProtocol.UnifiedPackedEquality.Column6.Codes
import Airbender.Import.GKRProtocol.BlockCoverageImport

namespace Airbender.Compiler.UnifiedPackedEquality.Column6
open Airbender Airbender.Compiler.PackedSetupEquality
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
-- Bind the complete fixed spans to the native columns.
set_option maxHeartbeats 4000000

column_blocks_part rawPrefix from Data.GKRSetup.Unified.setupColumn6 start 0 stop 128
column_blocks_part rawSource0 from Data.GKRSetup.Unified.setupColumn6 start 128 stop 24192
column_blocks_part rawSuffix from Data.GKRSetup.Unified.setupColumn6 start 24192 stop 24289
column_parts_cover sourceLayout from Data.GKRSetup.Unified.setupColumn6 parts [rawPrefix, rawSource0, rawSuffix]

setup_code_binding raw_source0_binding : rawSource0 = source0.map BlockCode.decode

private theorem source_shape : Data.GKRSetup.Unified.setupColumn6.blocks.toList = rawPrefix ++ rawSource0 ++ rawSuffix := by
  simpa only [List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc] using sourceLayout

theorem source0_binding : (Data.GKRSetup.Unified.setupColumn6.blocks.toList.drop 128).take 24064 = source0.map BlockCode.decode := by
  apply Eq.trans _ raw_source0_binding
  apply select_middle _ (rawPrefix) rawSource0 (rawSuffix) 128 24064
  · simpa only [List.append_assoc] using source_shape
  · decide +kernel
  · decide +kernel

theorem source_binding : (Data.GKRSetup.Unified.setupColumn6.blocks.toList.drop 128).take 24064 = sourceCode.map BlockCode.decode := by
  rw [source0_binding]
  simp only [sourceCode]

column_blocks_part rawShiftPrefix from (UnifiedReduced.Setup.nativeShiftData.columns[(6 : Nat)]) start 0 stop 128
column_blocks_part rawShift from (UnifiedReduced.Setup.nativeShiftData.columns[(6 : Nat)]) start 128 stop 24192
column_blocks_part rawShiftSuffix from (UnifiedReduced.Setup.nativeShiftData.columns[(6 : Nat)]) start 24192 stop 24287
column_parts_cover shiftLayout from (UnifiedReduced.Setup.nativeShiftData.columns[(6 : Nat)]) parts [rawShiftPrefix, rawShift, rawShiftSuffix]
setup_code_binding raw_shift_binding : rawShift = shiftCode.map BlockCode.decode

theorem shift_binding : ((UnifiedReduced.Setup.nativeShiftData.columns[(6 : Nat)]).blocks.toList.drop 128).take 24064 = shiftCode.map BlockCode.decode := by
  apply Eq.trans _ raw_shift_binding
  apply select_middle _ rawShiftPrefix rawShift rawShiftSuffix 128 24064
  · simpa only [List.flatten_cons, List.flatten_nil, List.append_nil, List.nil_append, List.append_assoc] using shiftLayout
  · decide +kernel
  · decide +kernel

theorem target_binding : ((UnifiedReduced.Setup.nativeShiftData.columns[(6 : Nat)]).blocks.toList.drop 128).take 24064 = targetCode.map BlockCode.decode := by
  rw [shift_binding]
  simp only [targetCode]

end Airbender.Compiler.UnifiedPackedEquality.Column6
