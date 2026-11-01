import Airbender.Proofs.GKRProtocol.FunctionalBaseChecks.WordMemoryUncached.Data
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.FunctionalBaseChecks.WordMemoryUncached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

numeric_data_binding view0 : (data.drop 0).take 8 = (data0.drop 0).take 8

numeric_data_binding piece0 : (data0.drop 0).take 8 = ((originalEntries.drop 0).take 8).map NumericFunctionalBaseChecks.encode

theorem binding0 : (data.drop 0).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 0).take 8 :=
  view0.trans (piece0.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 0 8))

numeric_data_binding view8 : (data.drop 8).take 1 = (data8.drop 0).take 1

numeric_data_binding piece8 : (data8.drop 0).take 1 = ((originalEntries.drop 8).take 1).map NumericFunctionalBaseChecks.encode

theorem binding8 : (data.drop 8).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 8).take 1 :=
  view8.trans (piece8.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 8 1))

theorem sourceNode0_9 : (data.drop 0).take 9 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 0).take 9 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 0 8 1 binding0 binding8

theorem source_binding : data = originalEntries.map NumericFunctionalBaseChecks.encode :=
  NumericQueryFrameChecks.complete_binding data (originalEntries.map NumericFunctionalBaseChecks.encode) 9
    (by decide +kernel) (by decide +kernel) sourceNode0_9

end Airbender.Compiler.FunctionalBaseChecks.WordMemoryUncached
