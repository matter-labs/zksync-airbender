module
import all Mathlib.Data.List.Sort
public import Proven.GKRProtocol.FunctionalBaseChecks.WordMemoryCached.Data
public import Proven.GKRProtocol.NumericQueryFrameBindings
public import Proven.Import.GKRProtocol.NumericArithmeticDataImport

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.FunctionalBaseChecks.WordMemoryCached
open Airbender.Compiler
set_option maxRecDepth 8192

numeric_data_binding view0 : (data.drop 0).take 8 = (data0.drop 0).take 8

numeric_data_binding piece0 : (data0.drop 0).take 8 = ((originalEntries.drop 0).take 8).map NumericFunctionalBaseChecks.encode

theorem binding0 : (data.drop 0).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 0).take 8 :=
  view0.trans (piece0.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 0 8))

numeric_data_binding view8 : (data.drop 8).take 7 = (data8.drop 0).take 7

numeric_data_binding piece8 : (data8.drop 0).take 7 = ((originalEntries.drop 8).take 7).map NumericFunctionalBaseChecks.encode

theorem binding8 : (data.drop 8).take 7 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 8).take 7 :=
  view8.trans (piece8.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 8 7))

theorem sourceNode0_15 : (data.drop 0).take 15 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 0).take 15 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 0 8 7 binding0 binding8

theorem source_binding : data = originalEntries.map NumericFunctionalBaseChecks.encode :=
  NumericQueryFrameChecks.complete_binding data (originalEntries.map NumericFunctionalBaseChecks.encode) 15
    (by decide +kernel) (by decide +kernel) sourceNode0_15

end Airbender.Compiler.FunctionalBaseChecks.WordMemoryCached
