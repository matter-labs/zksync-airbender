import Airbender.Proofs.GKRProtocol.CleanArgumentChecks.WordMemoryCached.Data
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.CleanArgumentChecks.WordMemoryCached
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

numeric_data_binding view16 : (data.drop 16).take 4 = (data16.drop 0).take 4

numeric_data_binding piece16 : (data16.drop 0).take 4 = ((originalEntries.drop 16).take 4).map NumericFunctionalBaseChecks.encode

theorem binding16 : (data.drop 16).take 4 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 16).take 4 :=
  view16.trans (piece16.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 16 4))

theorem sourceNode8_12 : (data.drop 8).take 12 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 8).take 12 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 8 8 4 binding8 binding16

theorem sourceNode0_20 : (data.drop 0).take 20 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 0).take 20 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 0 8 12 binding0 sourceNode8_12

theorem source_binding : data = originalEntries.map NumericFunctionalBaseChecks.encode :=
  NumericQueryFrameChecks.complete_binding data (originalEntries.map NumericFunctionalBaseChecks.encode) 20
    (by decide +kernel) (by decide +kernel) sourceNode0_20

end Airbender.Compiler.CleanArgumentChecks.WordMemoryCached
