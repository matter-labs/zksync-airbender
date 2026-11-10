import Airbender.Proofs.GKRProtocol.SourceFreshnessChecks.KeccakCached.Data
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.SourceFreshnessChecks.KeccakCached
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

numeric_data_binding view216 : (data.drop 216).take 6 = data216

numeric_data_binding piece216 : data216 = ((originalEntries.drop 216).take 6).map NumericFunctionalBaseChecks.encode

theorem binding216 : (data.drop 216).take 6 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 216).take 6 :=
  view216.trans (piece216.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 216 6))

theorem sourceNode8_16 : (data.drop 8).take 16 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 8).take 16 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 8 8 8 binding8 binding16

theorem sourceNode0_24 : (data.drop 0).take 24 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 0).take 24 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 0 8 16 binding0 sourceNode8_16

theorem sourceNode24_16 : (data.drop 24).take 16 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 24).take 16 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 24 8 8 binding24 binding32

theorem sourceNode40_16 : (data.drop 40).take 16 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 40).take 16 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 40 8 8 binding40 binding48

theorem sourceNode24_32 : (data.drop 24).take 32 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 24).take 32 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 24 16 16 sourceNode24_16 sourceNode40_16

theorem sourceNode0_56 : (data.drop 0).take 56 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 0).take 56 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 0 24 32 sourceNode0_24 sourceNode24_32

theorem sourceNode64_16 : (data.drop 64).take 16 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 64).take 16 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 64 8 8 binding64 binding72

theorem sourceNode56_24 : (data.drop 56).take 24 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 56).take 24 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 56 8 16 binding56 sourceNode64_16

theorem sourceNode80_16 : (data.drop 80).take 16 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 80).take 16 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 80 8 8 binding80 binding88

theorem sourceNode96_16 : (data.drop 96).take 16 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 96).take 16 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 96 8 8 binding96 binding104

theorem sourceNode80_32 : (data.drop 80).take 32 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 80).take 32 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 80 16 16 sourceNode80_16 sourceNode96_16

theorem sourceNode56_56 : (data.drop 56).take 56 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 56).take 56 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 56 24 32 sourceNode56_24 sourceNode80_32

theorem sourceNode0_112 : (data.drop 0).take 112 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 0).take 112 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 0 56 56 sourceNode0_56 sourceNode56_56

theorem sourceNode120_16 : (data.drop 120).take 16 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 120).take 16 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 120 8 8 binding120 binding128

theorem sourceNode112_24 : (data.drop 112).take 24 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 112).take 24 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 112 8 16 binding112 sourceNode120_16

theorem sourceNode136_16 : (data.drop 136).take 16 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 136).take 16 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 136 8 8 binding136 binding144

theorem sourceNode152_16 : (data.drop 152).take 16 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 152).take 16 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 152 8 8 binding152 binding160

theorem sourceNode136_32 : (data.drop 136).take 32 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 136).take 32 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 136 16 16 sourceNode136_16 sourceNode152_16

theorem sourceNode112_56 : (data.drop 112).take 56 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 112).take 56 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 112 24 32 sourceNode112_24 sourceNode136_32

theorem sourceNode176_16 : (data.drop 176).take 16 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 176).take 16 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 176 8 8 binding176 binding184

theorem sourceNode168_24 : (data.drop 168).take 24 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 168).take 24 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 168 8 16 binding168 sourceNode176_16

theorem sourceNode192_16 : (data.drop 192).take 16 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 192).take 16 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 192 8 8 binding192 binding200

theorem sourceNode208_14 : (data.drop 208).take 14 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 208).take 14 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 208 8 6 binding208 binding216

theorem sourceNode192_30 : (data.drop 192).take 30 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 192).take 30 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 192 16 14 sourceNode192_16 sourceNode208_14

theorem sourceNode168_54 : (data.drop 168).take 54 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 168).take 54 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 168 24 30 sourceNode168_24 sourceNode192_30

theorem sourceNode112_110 : (data.drop 112).take 110 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 112).take 110 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 112 56 54 sourceNode112_56 sourceNode168_54

theorem sourceNode0_222 : (data.drop 0).take 222 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 0).take 222 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 0 112 110 sourceNode0_112 sourceNode112_110

theorem raw_binding : data = originalEntries.map NumericFunctionalBaseChecks.encode :=
  NumericQueryFrameChecks.complete_binding data (originalEntries.map NumericFunctionalBaseChecks.encode) 222
    (by decide +kernel) (by decide +kernel) sourceNode0_222

theorem source_binding : data = NumericSourceFreshnessChecks.encodeAddresses sourceAddresses := by
  simpa only [originalEntries, NumericSourceFreshnessChecks.encodeAddresses, List.map_map, Function.comp_def] using raw_binding

numeric_data_binding target_binding : targetData = NumericSourceFreshnessChecks.encodeAddresses targetAddresses

end Airbender.Compiler.SourceFreshnessChecks.KeccakCached
