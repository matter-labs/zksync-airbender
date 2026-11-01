import Airbender.Import.PackedSetupEmbed
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport
import Airbender.Proofs.GKRProtocol.PackedSetupNormalization
import Airbender.Data.GKRSetup.SubwordMemory

namespace Tests.PackedSubwordCodes
open Airbender Airbender.Compiler PackedSetupEquality
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

import_setup_code_capture from "artifacts/setup/subword-memory.json" [
  codes0 := column 1 block_start 2 block_count 1 unpacked,
  codes1 := column 1 block_start 8 block_count 1 unpacked,
  codes2 := column 1 block_start 11 block_count 1 unpacked,
  codes3 := column 2 block_start 3 block_count 1 unpacked]

numeric_data_binding binding0 : (Data.GKRSetup.SubwordMemory.setupColumn1.blocks.toList.drop 2).take 1 = codes0.map BlockCode.decode
numeric_data_binding binding1 : (Data.GKRSetup.SubwordMemory.setupColumn1.blocks.toList.drop 8).take 1 = codes1.map BlockCode.decode
numeric_data_binding binding2 : (Data.GKRSetup.SubwordMemory.setupColumn1.blocks.toList.drop 11).take 1 = codes2.map BlockCode.decode
numeric_data_binding binding3 : (Data.GKRSetup.SubwordMemory.setupColumn2.blocks.toList.drop 3).take 1 = codes3.map BlockCode.decode

theorem arithmetic_recipe : codes0 = [.periodic 256 0 (.linearRuns 256 0 256 1)] := by decide +kernel

theorem wrapped_recipe : codes1 = [.periodic 256 0
    (.append (.linearRuns 128 0 1 1) (.linearRuns 128 65408 1 1))] := by decide +kernel

theorem constant_recipe : codes2 = [.periodic 128 1 (.constant 256 65408)] := by decide +kernel

theorem lookup_recipe : codes3 = [.periodic 256 0
    (.lookupRuns 256 128 (.append (.constant 1 65535) (.constant 1 0)))] := by decide +kernel

def requests : List PackedSetupNormalization.Request := [⟨codes0, codes0, 65536⟩, ⟨codes1, codes1, 65536⟩, ⟨codes2, codes2, 32768⟩, ⟨codes3, codes3, 65536⟩]

theorem checked : PackedSetupNormalization.check requests = true := by decide +kernel

end Tests.PackedSubwordCodes
