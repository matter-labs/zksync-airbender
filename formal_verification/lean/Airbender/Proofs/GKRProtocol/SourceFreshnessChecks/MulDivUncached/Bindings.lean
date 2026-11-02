import Airbender.Proofs.GKRProtocol.SourceFreshnessChecks.MulDivUncached.Data
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.SourceFreshnessChecks.MulDivUncached
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

numeric_data_binding view64 : (data.drop 64).take 1 = data64

numeric_data_binding piece64 : data64 = ((originalEntries.drop 64).take 1).map NumericFunctionalBaseChecks.encode

theorem binding64 : (data.drop 64).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 64).take 1 :=
  view64.trans (piece64.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 64 1))

theorem sourceNode0_16 : (data.drop 0).take 16 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 0).take 16 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 0 8 8 binding0 binding8

theorem sourceNode16_16 : (data.drop 16).take 16 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 16).take 16 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 16 8 8 binding16 binding24

theorem sourceNode0_32 : (data.drop 0).take 32 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 0).take 32 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 0 16 16 sourceNode0_16 sourceNode16_16

theorem sourceNode32_16 : (data.drop 32).take 16 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 32).take 16 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 32 8 8 binding32 binding40

theorem sourceNode56_9 : (data.drop 56).take 9 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 56).take 9 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 56 8 1 binding56 binding64

theorem sourceNode48_17 : (data.drop 48).take 17 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 48).take 17 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 48 8 9 binding48 sourceNode56_9

theorem sourceNode32_33 : (data.drop 32).take 33 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 32).take 33 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 32 16 17 sourceNode32_16 sourceNode48_17

theorem sourceNode0_65 : (data.drop 0).take 65 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 0).take 65 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 0 32 33 sourceNode0_32 sourceNode32_33

theorem raw_binding : data = originalEntries.map NumericFunctionalBaseChecks.encode :=
  NumericQueryFrameChecks.complete_binding data (originalEntries.map NumericFunctionalBaseChecks.encode) 65
    (by decide +kernel) (by decide +kernel) sourceNode0_65

theorem source_binding : data = NumericSourceFreshnessChecks.encodeAddresses sourceAddresses := by
  simpa only [originalEntries, NumericSourceFreshnessChecks.encodeAddresses, List.map_map, Function.comp_def] using raw_binding

numeric_data_binding target_binding : targetData = NumericSourceFreshnessChecks.encodeAddresses targetAddresses

end Airbender.Compiler.SourceFreshnessChecks.MulDivUncached
