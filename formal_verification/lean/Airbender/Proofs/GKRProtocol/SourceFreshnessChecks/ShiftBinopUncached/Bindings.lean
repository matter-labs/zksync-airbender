import Airbender.Proofs.GKRProtocol.SourceFreshnessChecks.ShiftBinopUncached.Data
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.SourceFreshnessChecks.ShiftBinopUncached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

numeric_data_binding view0 : (data.drop 0).take 8 = data0

numeric_data_binding piece0 : data0 = ((originalEntries.drop 0).take 8).map NumericFunctionalBaseChecks.encode

theorem binding0 : (data.drop 0).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 0).take 8 :=
  view0.trans (piece0.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 0 8))

numeric_data_binding view8 : (data.drop 8).take 8 = data8

numeric_data_binding piece8 : data8 = ((originalEntries.drop 8).take 8).map NumericFunctionalBaseChecks.encode

theorem binding8 : (data.drop 8).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 8).take 8 :=
  view8.trans (piece8.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 8 8))

numeric_data_binding view16 : (data.drop 16).take 8 = data16

numeric_data_binding piece16 : data16 = ((originalEntries.drop 16).take 8).map NumericFunctionalBaseChecks.encode

theorem binding16 : (data.drop 16).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 16).take 8 :=
  view16.trans (piece16.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 16 8))

numeric_data_binding view24 : (data.drop 24).take 8 = data24

numeric_data_binding piece24 : data24 = ((originalEntries.drop 24).take 8).map NumericFunctionalBaseChecks.encode

theorem binding24 : (data.drop 24).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 24).take 8 :=
  view24.trans (piece24.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 24 8))

numeric_data_binding view32 : (data.drop 32).take 8 = data32

numeric_data_binding piece32 : data32 = ((originalEntries.drop 32).take 8).map NumericFunctionalBaseChecks.encode

theorem binding32 : (data.drop 32).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 32).take 8 :=
  view32.trans (piece32.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 32 8))

numeric_data_binding view40 : (data.drop 40).take 8 = data40

numeric_data_binding piece40 : data40 = ((originalEntries.drop 40).take 8).map NumericFunctionalBaseChecks.encode

theorem binding40 : (data.drop 40).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 40).take 8 :=
  view40.trans (piece40.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 40 8))

numeric_data_binding view48 : (data.drop 48).take 8 = data48

numeric_data_binding piece48 : data48 = ((originalEntries.drop 48).take 8).map NumericFunctionalBaseChecks.encode

theorem binding48 : (data.drop 48).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 48).take 8 :=
  view48.trans (piece48.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 48 8))

numeric_data_binding view56 : (data.drop 56).take 8 = data56

numeric_data_binding piece56 : data56 = ((originalEntries.drop 56).take 8).map NumericFunctionalBaseChecks.encode

theorem binding56 : (data.drop 56).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 56).take 8 :=
  view56.trans (piece56.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 56 8))

numeric_data_binding view64 : (data.drop 64).take 8 = data64

numeric_data_binding piece64 : data64 = ((originalEntries.drop 64).take 8).map NumericFunctionalBaseChecks.encode

theorem binding64 : (data.drop 64).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 64).take 8 :=
  view64.trans (piece64.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 64 8))

numeric_data_binding view72 : (data.drop 72).take 8 = data72

numeric_data_binding piece72 : data72 = ((originalEntries.drop 72).take 8).map NumericFunctionalBaseChecks.encode

theorem binding72 : (data.drop 72).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 72).take 8 :=
  view72.trans (piece72.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 72 8))

numeric_data_binding view80 : (data.drop 80).take 8 = data80

numeric_data_binding piece80 : data80 = ((originalEntries.drop 80).take 8).map NumericFunctionalBaseChecks.encode

theorem binding80 : (data.drop 80).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 80).take 8 :=
  view80.trans (piece80.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 80 8))

numeric_data_binding view88 : (data.drop 88).take 4 = data88

numeric_data_binding piece88 : data88 = ((originalEntries.drop 88).take 4).map NumericFunctionalBaseChecks.encode

theorem binding88 : (data.drop 88).take 4 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 88).take 4 :=
  view88.trans (piece88.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 88 4))

theorem sourceNode8_16 : (data.drop 8).take 16 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 8).take 16 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 8 8 8 binding8 binding16

theorem sourceNode0_24 : (data.drop 0).take 24 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 0).take 24 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 0 8 16 binding0 sourceNode8_16

theorem sourceNode32_16 : (data.drop 32).take 16 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 32).take 16 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 32 8 8 binding32 binding40

theorem sourceNode24_24 : (data.drop 24).take 24 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 24).take 24 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 24 8 16 binding24 sourceNode32_16

theorem sourceNode0_48 : (data.drop 0).take 48 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 0).take 48 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 0 24 24 sourceNode0_24 sourceNode24_24

theorem sourceNode56_16 : (data.drop 56).take 16 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 56).take 16 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 56 8 8 binding56 binding64

theorem sourceNode48_24 : (data.drop 48).take 24 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 48).take 24 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 48 8 16 binding48 sourceNode56_16

theorem sourceNode80_12 : (data.drop 80).take 12 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 80).take 12 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 80 8 4 binding80 binding88

theorem sourceNode72_20 : (data.drop 72).take 20 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 72).take 20 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 72 8 12 binding72 sourceNode80_12

theorem sourceNode48_44 : (data.drop 48).take 44 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 48).take 44 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 48 24 20 sourceNode48_24 sourceNode72_20

theorem sourceNode0_92 : (data.drop 0).take 92 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 0).take 92 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 0 48 44 sourceNode0_48 sourceNode48_44

theorem raw_binding : data = originalEntries.map NumericFunctionalBaseChecks.encode :=
  NumericQueryFrameChecks.complete_binding data (originalEntries.map NumericFunctionalBaseChecks.encode) 92
    (by decide +kernel) (by decide +kernel) sourceNode0_92

theorem source_binding : data = NumericSourceFreshnessChecks.encodeAddresses sourceAddresses := by
  simpa only [originalEntries, NumericSourceFreshnessChecks.encodeAddresses, List.map_map, Function.comp_def] using raw_binding

numeric_data_binding target_binding : targetData = NumericSourceFreshnessChecks.encodeAddresses targetAddresses

end Airbender.Compiler.SourceFreshnessChecks.ShiftBinopUncached
