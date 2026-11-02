import Airbender.Proofs.GKRProtocol.SourceFreshnessChecks.AddSubUncached.Data
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.SourceFreshnessChecks.AddSubUncached
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

numeric_data_binding view40 : (data.drop 40).take 2 = data40

numeric_data_binding piece40 : data40 = ((originalEntries.drop 40).take 2).map NumericFunctionalBaseChecks.encode

theorem binding40 : (data.drop 40).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 40).take 2 :=
  view40.trans (piece40.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 40 2))

theorem sourceNode8_16 : (data.drop 8).take 16 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 8).take 16 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 8 8 8 binding8 binding16

theorem sourceNode0_24 : (data.drop 0).take 24 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 0).take 24 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 0 8 16 binding0 sourceNode8_16

theorem sourceNode32_10 : (data.drop 32).take 10 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 32).take 10 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 32 8 2 binding32 binding40

theorem sourceNode24_18 : (data.drop 24).take 18 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 24).take 18 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 24 8 10 binding24 sourceNode32_10

theorem sourceNode0_42 : (data.drop 0).take 42 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 0).take 42 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 0 24 18 sourceNode0_24 sourceNode24_18

theorem raw_binding : data = originalEntries.map NumericFunctionalBaseChecks.encode :=
  NumericQueryFrameChecks.complete_binding data (originalEntries.map NumericFunctionalBaseChecks.encode) 42
    (by decide +kernel) (by decide +kernel) sourceNode0_42

theorem source_binding : data = NumericSourceFreshnessChecks.encodeAddresses sourceAddresses := by
  simpa only [originalEntries, NumericSourceFreshnessChecks.encodeAddresses, List.map_map, Function.comp_def] using raw_binding

numeric_data_binding target_binding : targetData = NumericSourceFreshnessChecks.encodeAddresses targetAddresses

end Airbender.Compiler.SourceFreshnessChecks.AddSubUncached
