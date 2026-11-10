import Airbender.Proofs.GKRProtocol.FunctionalBaseChecks.BlakeGCached.Data
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.FunctionalBaseChecks.BlakeGCached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

numeric_data_binding view0 : (data.drop 0).take 8 = (data0.drop 0).take 8

numeric_data_binding piece0 : (data0.drop 0).take 8 = ((originalEntries.drop 0).take 8).map NumericFunctionalBaseChecks.encode

theorem binding0 : (data.drop 0).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 0).take 8 :=
  view0.trans (piece0.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 0 8))

numeric_data_binding view8 : (data.drop 8).take 8 = (data8.drop 0).take 8

numeric_data_binding piece8 : (data8.drop 0).take 8 = ((originalEntries.drop 8).take 8).map NumericFunctionalBaseChecks.encode

theorem binding8 : (data.drop 8).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 8).take 8 :=
  view8.trans (piece8.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 8 8))

numeric_data_binding view16 : (data.drop 16).take 8 = (data16.drop 0).take 8

numeric_data_binding piece16 : (data16.drop 0).take 8 = ((originalEntries.drop 16).take 8).map NumericFunctionalBaseChecks.encode

theorem binding16 : (data.drop 16).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 16).take 8 :=
  view16.trans (piece16.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 16 8))

numeric_data_binding view24 : (data.drop 24).take 1 = (data24.drop 0).take 1

numeric_data_binding piece24 : (data24.drop 0).take 1 = ((originalEntries.drop 24).take 1).map NumericFunctionalBaseChecks.encode

theorem binding24 : (data.drop 24).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 24).take 1 :=
  view24.trans (piece24.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 24 1))

theorem sourceNode0_16 : (data.drop 0).take 16 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 0).take 16 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 0 8 8 binding0 binding8

theorem sourceNode16_9 : (data.drop 16).take 9 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 16).take 9 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 16 8 1 binding16 binding24

theorem sourceNode0_25 : (data.drop 0).take 25 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 0).take 25 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 0 16 9 sourceNode0_16 sourceNode16_9

theorem source_binding : data = originalEntries.map NumericFunctionalBaseChecks.encode :=
  NumericQueryFrameChecks.complete_binding data (originalEntries.map NumericFunctionalBaseChecks.encode) 25
    (by decide +kernel) (by decide +kernel) sourceNode0_25

end Airbender.Compiler.FunctionalBaseChecks.BlakeGCached
