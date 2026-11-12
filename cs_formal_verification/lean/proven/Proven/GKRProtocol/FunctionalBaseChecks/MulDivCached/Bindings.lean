module
import all Mathlib.Data.List.Sort
public import Proven.GKRProtocol.FunctionalBaseChecks.MulDivCached.Data
public import Proven.GKRProtocol.NumericQueryFrameBindings
public import Proven.Import.GKRProtocol.NumericArithmeticDataImport

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.FunctionalBaseChecks.MulDivCached
open Airbender.Compiler
set_option maxRecDepth 8192

numeric_data_binding view0 : (data.drop 0).take 8 = (data0.drop 0).take 8

numeric_data_binding piece0 : (data0.drop 0).take 8 = ((originalEntries.drop 0).take 8).map NumericFunctionalBaseChecks.encode

theorem binding0 : (data.drop 0).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 0).take 8 :=
  view0.trans (piece0.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 0 8))

numeric_data_binding view8 : (data.drop 8).take 8 = (data8.drop 0).take 8

numeric_data_binding piece8 : (data8.drop 0).take 8 = ((originalEntries.drop 8).take 8).map NumericFunctionalBaseChecks.encode

theorem binding8 : (data.drop 8).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 8).take 8 :=
  view8.trans (piece8.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 8 8))

numeric_data_binding view16 : (data.drop 16).take 3 = (data16.drop 0).take 3

numeric_data_binding piece16 : (data16.drop 0).take 3 = ((originalEntries.drop 16).take 3).map NumericFunctionalBaseChecks.encode

theorem binding16 : (data.drop 16).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 16).take 3 :=
  view16.trans (piece16.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 16 3))

theorem sourceNode8_11 : (data.drop 8).take 11 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 8).take 11 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 8 8 3 binding8 binding16

theorem sourceNode0_19 : (data.drop 0).take 19 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 0).take 19 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 0 8 11 binding0 sourceNode8_11

theorem source_binding : data = originalEntries.map NumericFunctionalBaseChecks.encode :=
  NumericQueryFrameChecks.complete_binding data (originalEntries.map NumericFunctionalBaseChecks.encode) 19
    (by decide +kernel) (by decide +kernel) sourceNode0_19

end Airbender.Compiler.FunctionalBaseChecks.MulDivCached
