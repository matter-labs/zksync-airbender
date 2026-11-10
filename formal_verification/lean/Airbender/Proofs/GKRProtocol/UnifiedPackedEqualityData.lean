import Airbender.Proofs.GKRProtocol.UnifiedPackedEqualityCodes
import Airbender.Import.GKRProtocol.BlockCoverageImport

namespace Airbender.Compiler.UnifiedPackedEquality
open Airbender Airbender.Compiler.PackedSetupEquality
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072

-- These data views select one complete fixed-column capture. The generic
-- coverage proof binds them to the original column.
column_blocks_part rawPrefix from Data.GKRSetup.Unified.setupColumn2 start 0 stop 128
column_blocks_part rawOriginal from Data.GKRSetup.Unified.setupColumn2 start 128 stop 2712
column_blocks_part rawSuffix from Data.GKRSetup.Unified.setupColumn2 start 2712 stop 2715
column_parts_cover sourceLayout from Data.GKRSetup.Unified.setupColumn2
  parts [rawPrefix, rawOriginal, rawSuffix]

setup_code_binding raw_source_binding : rawOriginal = sourceCode.map BlockCode.decode

theorem source_binding :
    (Data.GKRSetup.Unified.setupColumn2.blocks.toList.drop 128).take 2584 =
      sourceCode.map BlockCode.decode := by
  apply Eq.trans _ raw_source_binding
  apply select_middle _ rawPrefix rawOriginal rawSuffix 128 2584
  · simpa only [List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc] using sourceLayout
  · decide +kernel
  · decide +kernel

column_blocks_part rawXorPrefix from (UnifiedReduced.Setup.nativeXorData.columns[(2 : Nat)]) start 0 stop 111
column_blocks_part rawXor from (UnifiedReduced.Setup.nativeXorData.columns[(2 : Nat)]) start 111 stop 899
column_parts_cover xorLayout from (UnifiedReduced.Setup.nativeXorData.columns[(2 : Nat)])
  parts [rawXorPrefix, rawXor]
column_blocks_part rawOr from (UnifiedReduced.Setup.nativeOrData.columns[(2 : Nat)]) start 0 stop 898
column_parts_cover orLayout from (UnifiedReduced.Setup.nativeOrData.columns[(2 : Nat)]) parts [rawOr]
column_blocks_part rawAnd from (UnifiedReduced.Setup.nativeAndData.columns[(2 : Nat)]) start 0 stop 898
column_parts_cover andLayout from (UnifiedReduced.Setup.nativeAndData.columns[(2 : Nat)]) parts [rawAnd]

setup_code_binding raw_target_binding :
    rawXor ++ rawOr ++ rawAnd = targetCode.map BlockCode.decode

theorem target_binding :
    (UnifiedReduced.Setup.nativeXorData.columns[2].blocks.toList.drop 111).take 788 ++
    UnifiedReduced.Setup.nativeOrData.columns[2].blocks.toList ++
    UnifiedReduced.Setup.nativeAndData.columns[2].blocks.toList =
      targetCode.map BlockCode.decode := by
  have xorSelected : (UnifiedReduced.Setup.nativeXorData.columns[2].blocks.toList.drop 111).take 788 = rawXor := by
    apply select_middle _ rawXorPrefix rawXor [] 111 788
    · simpa only [List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc] using xorLayout
    · decide +kernel
    · decide +kernel
  have orSelected : UnifiedReduced.Setup.nativeOrData.columns[2].blocks.toList = rawOr := by
    simpa only [List.flatten_cons, List.flatten_nil, List.append_nil] using orLayout
  have andSelected : UnifiedReduced.Setup.nativeAndData.columns[2].blocks.toList = rawAnd := by
    simpa only [List.flatten_cons, List.flatten_nil, List.append_nil] using andLayout
  rw [xorSelected, orSelected, andSelected]
  exact raw_target_binding

end Airbender.Compiler.UnifiedPackedEquality
