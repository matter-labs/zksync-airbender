import Airbender.Proofs.GKRProtocol.SourceFreshnessChecks.BigintCached.Data
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.SourceFreshnessChecks.BigintCached
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

numeric_data_binding view120 : (data.drop 120).take 8 = data120

numeric_data_binding piece120 : data120 = ((originalEntries.drop 120).take 8).map NumericFunctionalBaseChecks.encode

theorem binding120 : (data.drop 120).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 120).take 8 :=
  view120.trans (piece120.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 120 8))

numeric_data_binding view128 : (data.drop 128).take 8 = data128

numeric_data_binding piece128 : data128 = ((originalEntries.drop 128).take 8).map NumericFunctionalBaseChecks.encode

theorem binding128 : (data.drop 128).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 128).take 8 :=
  view128.trans (piece128.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 128 8))

numeric_data_binding view136 : (data.drop 136).take 8 = data136

numeric_data_binding piece136 : data136 = ((originalEntries.drop 136).take 8).map NumericFunctionalBaseChecks.encode

theorem binding136 : (data.drop 136).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 136).take 8 :=
  view136.trans (piece136.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 136 8))

numeric_data_binding view144 : (data.drop 144).take 8 = data144

numeric_data_binding piece144 : data144 = ((originalEntries.drop 144).take 8).map NumericFunctionalBaseChecks.encode

theorem binding144 : (data.drop 144).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 144).take 8 :=
  view144.trans (piece144.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 144 8))

numeric_data_binding view152 : (data.drop 152).take 8 = data152

numeric_data_binding piece152 : data152 = ((originalEntries.drop 152).take 8).map NumericFunctionalBaseChecks.encode

theorem binding152 : (data.drop 152).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 152).take 8 :=
  view152.trans (piece152.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 152 8))

numeric_data_binding view160 : (data.drop 160).take 8 = data160

numeric_data_binding piece160 : data160 = ((originalEntries.drop 160).take 8).map NumericFunctionalBaseChecks.encode

theorem binding160 : (data.drop 160).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 160).take 8 :=
  view160.trans (piece160.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 160 8))

numeric_data_binding view168 : (data.drop 168).take 8 = data168

numeric_data_binding piece168 : data168 = ((originalEntries.drop 168).take 8).map NumericFunctionalBaseChecks.encode

theorem binding168 : (data.drop 168).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 168).take 8 :=
  view168.trans (piece168.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 168 8))

numeric_data_binding view176 : (data.drop 176).take 8 = data176

numeric_data_binding piece176 : data176 = ((originalEntries.drop 176).take 8).map NumericFunctionalBaseChecks.encode

theorem binding176 : (data.drop 176).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 176).take 8 :=
  view176.trans (piece176.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 176 8))

numeric_data_binding view184 : (data.drop 184).take 8 = data184

numeric_data_binding piece184 : data184 = ((originalEntries.drop 184).take 8).map NumericFunctionalBaseChecks.encode

theorem binding184 : (data.drop 184).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 184).take 8 :=
  view184.trans (piece184.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 184 8))

numeric_data_binding view192 : (data.drop 192).take 8 = data192

numeric_data_binding piece192 : data192 = ((originalEntries.drop 192).take 8).map NumericFunctionalBaseChecks.encode

theorem binding192 : (data.drop 192).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 192).take 8 :=
  view192.trans (piece192.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 192 8))

numeric_data_binding view200 : (data.drop 200).take 8 = data200

numeric_data_binding piece200 : data200 = ((originalEntries.drop 200).take 8).map NumericFunctionalBaseChecks.encode

theorem binding200 : (data.drop 200).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 200).take 8 :=
  view200.trans (piece200.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 200 8))

numeric_data_binding view208 : (data.drop 208).take 8 = data208

numeric_data_binding piece208 : data208 = ((originalEntries.drop 208).take 8).map NumericFunctionalBaseChecks.encode

theorem binding208 : (data.drop 208).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 208).take 8 :=
  view208.trans (piece208.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 208 8))

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

theorem sourceNode72_16 : (data.drop 72).take 16 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 72).take 16 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 72 8 8 binding72 binding80

theorem sourceNode88_16 : (data.drop 88).take 16 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 88).take 16 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 88 8 8 binding88 binding96

theorem sourceNode72_32 : (data.drop 72).take 32 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 72).take 32 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 72 16 16 sourceNode72_16 sourceNode88_16

theorem sourceNode48_56 : (data.drop 48).take 56 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 48).take 56 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 48 24 32 sourceNode48_24 sourceNode72_32

theorem sourceNode0_104 : (data.drop 0).take 104 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 0).take 104 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 0 48 56 sourceNode0_48 sourceNode48_56

theorem sourceNode112_16 : (data.drop 112).take 16 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 112).take 16 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 112 8 8 binding112 binding120

theorem sourceNode104_24 : (data.drop 104).take 24 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 104).take 24 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 104 8 16 binding104 sourceNode112_16

theorem sourceNode128_16 : (data.drop 128).take 16 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 128).take 16 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 128 8 8 binding128 binding136

theorem sourceNode144_16 : (data.drop 144).take 16 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 144).take 16 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 144 8 8 binding144 binding152

theorem sourceNode128_32 : (data.drop 128).take 32 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 128).take 32 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 128 16 16 sourceNode128_16 sourceNode144_16

theorem sourceNode104_56 : (data.drop 104).take 56 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 104).take 56 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 104 24 32 sourceNode104_24 sourceNode128_32

theorem sourceNode168_16 : (data.drop 168).take 16 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 168).take 16 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 168 8 8 binding168 binding176

theorem sourceNode160_24 : (data.drop 160).take 24 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 160).take 24 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 160 8 16 binding160 sourceNode168_16

theorem sourceNode184_16 : (data.drop 184).take 16 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 184).take 16 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 184 8 8 binding184 binding192

theorem sourceNode200_16 : (data.drop 200).take 16 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 200).take 16 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 200 8 8 binding200 binding208

theorem sourceNode184_32 : (data.drop 184).take 32 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 184).take 32 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 184 16 16 sourceNode184_16 sourceNode200_16

theorem sourceNode160_56 : (data.drop 160).take 56 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 160).take 56 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 160 24 32 sourceNode160_24 sourceNode184_32

theorem sourceNode104_112 : (data.drop 104).take 112 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 104).take 112 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 104 56 56 sourceNode104_56 sourceNode160_56

theorem sourceNode0_216 : (data.drop 0).take 216 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 0).take 216 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 0 104 112 sourceNode0_104 sourceNode104_112

theorem raw_binding : data = originalEntries.map NumericFunctionalBaseChecks.encode :=
  NumericQueryFrameChecks.complete_binding data (originalEntries.map NumericFunctionalBaseChecks.encode) 216
    (by decide +kernel) (by decide +kernel) sourceNode0_216

theorem source_binding : data = NumericSourceFreshnessChecks.encodeAddresses sourceAddresses := by
  simpa only [originalEntries, NumericSourceFreshnessChecks.encodeAddresses, List.map_map, Function.comp_def] using raw_binding

numeric_data_binding target_binding : targetData = NumericSourceFreshnessChecks.encodeAddresses targetAddresses

end Airbender.Compiler.SourceFreshnessChecks.BigintCached
