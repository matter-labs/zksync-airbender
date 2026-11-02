import Airbender.Proofs.GKRProtocol.SourceFreshnessChecks.UnifiedUncached.Data
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.SourceFreshnessChecks.UnifiedUncached
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

numeric_data_binding view88 : (data.drop 88).take 8 = data88

numeric_data_binding piece88 : data88 = ((originalEntries.drop 88).take 8).map NumericFunctionalBaseChecks.encode

theorem binding88 : (data.drop 88).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 88).take 8 :=
  view88.trans (piece88.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 88 8))

numeric_data_binding view96 : (data.drop 96).take 8 = data96

numeric_data_binding piece96 : data96 = ((originalEntries.drop 96).take 8).map NumericFunctionalBaseChecks.encode

theorem binding96 : (data.drop 96).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 96).take 8 :=
  view96.trans (piece96.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 96 8))

numeric_data_binding view104 : (data.drop 104).take 8 = data104

numeric_data_binding piece104 : data104 = ((originalEntries.drop 104).take 8).map NumericFunctionalBaseChecks.encode

theorem binding104 : (data.drop 104).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 104).take 8 :=
  view104.trans (piece104.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 104 8))

numeric_data_binding view112 : (data.drop 112).take 8 = data112

numeric_data_binding piece112 : data112 = ((originalEntries.drop 112).take 8).map NumericFunctionalBaseChecks.encode

theorem binding112 : (data.drop 112).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 112).take 8 :=
  view112.trans (piece112.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 112 8))

numeric_data_binding view120 : (data.drop 120).take 3 = data120

numeric_data_binding piece120 : data120 = ((originalEntries.drop 120).take 3).map NumericFunctionalBaseChecks.encode

theorem binding120 : (data.drop 120).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 120).take 3 :=
  view120.trans (piece120.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 120 3))

theorem sourceNode0_16 : (data.drop 0).take 16 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 0).take 16 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 0 8 8 binding0 binding8

theorem sourceNode16_16 : (data.drop 16).take 16 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 16).take 16 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 16 8 8 binding16 binding24

theorem sourceNode0_32 : (data.drop 0).take 32 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 0).take 32 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 0 16 16 sourceNode0_16 sourceNode16_16

theorem sourceNode32_16 : (data.drop 32).take 16 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 32).take 16 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 32 8 8 binding32 binding40

theorem sourceNode48_16 : (data.drop 48).take 16 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 48).take 16 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 48 8 8 binding48 binding56

theorem sourceNode32_32 : (data.drop 32).take 32 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 32).take 32 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 32 16 16 sourceNode32_16 sourceNode48_16

theorem sourceNode0_64 : (data.drop 0).take 64 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 0).take 64 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 0 32 32 sourceNode0_32 sourceNode32_32

theorem sourceNode64_16 : (data.drop 64).take 16 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 64).take 16 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 64 8 8 binding64 binding72

theorem sourceNode80_16 : (data.drop 80).take 16 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 80).take 16 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 80 8 8 binding80 binding88

theorem sourceNode64_32 : (data.drop 64).take 32 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 64).take 32 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 64 16 16 sourceNode64_16 sourceNode80_16

theorem sourceNode96_16 : (data.drop 96).take 16 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 96).take 16 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 96 8 8 binding96 binding104

theorem sourceNode112_11 : (data.drop 112).take 11 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 112).take 11 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 112 8 3 binding112 binding120

theorem sourceNode96_27 : (data.drop 96).take 27 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 96).take 27 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 96 16 11 sourceNode96_16 sourceNode112_11

theorem sourceNode64_59 : (data.drop 64).take 59 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 64).take 59 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 64 32 27 sourceNode64_32 sourceNode96_27

theorem sourceNode0_123 : (data.drop 0).take 123 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 0).take 123 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 0 64 59 sourceNode0_64 sourceNode64_59

theorem raw_binding : data = originalEntries.map NumericFunctionalBaseChecks.encode :=
  NumericQueryFrameChecks.complete_binding data (originalEntries.map NumericFunctionalBaseChecks.encode) 123
    (by decide +kernel) (by decide +kernel) sourceNode0_123

theorem source_binding : data = NumericSourceFreshnessChecks.encodeAddresses sourceAddresses := by
  simpa only [originalEntries, NumericSourceFreshnessChecks.encodeAddresses, List.map_map, Function.comp_def] using raw_binding

numeric_data_binding target_binding : targetData = NumericSourceFreshnessChecks.encodeAddresses targetAddresses

end Airbender.Compiler.SourceFreshnessChecks.UnifiedUncached
