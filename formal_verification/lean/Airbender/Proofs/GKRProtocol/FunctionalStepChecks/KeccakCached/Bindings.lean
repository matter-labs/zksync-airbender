import Airbender.Proofs.GKRProtocol.FunctionalStepChecks.KeccakCached.Data
import Airbender.Proofs.GKRProtocol.FunctionalNative.KeccakCachedFoundation
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.FunctionalStepChecks.KeccakCached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def encodePort (step : FunctionalStep) := NumericFunctionalStepChecks.encode Airbender.Compiler.FunctionalNative.KeccakCached.native.isBase ([], step)

noncomputable def sourcePorts := Airbender.Compiler.FunctionalNative.KeccakCached.native.program.map encodePort

numeric_data_binding portsView0 : (ports.drop 0).take 8 = (ports0.drop 0).take 8

numeric_data_binding portsPiece0 : (ports0.drop 0).take 8 = ((Airbender.Compiler.FunctionalNative.KeccakCached.native.program.drop 0).take 8).map encodePort

theorem portsSlice0 : (ports.drop 0).take 8 = (sourcePorts.drop 0).take 8 :=
  portsView0.trans (portsPiece0.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.KeccakCached.native.program encodePort 0 8))

numeric_data_binding portsView8 : (ports.drop 8).take 8 = (ports0.drop 8).take 8

numeric_data_binding portsPiece8 : (ports0.drop 8).take 8 = ((Airbender.Compiler.FunctionalNative.KeccakCached.native.program.drop 8).take 8).map encodePort

theorem portsSlice8 : (ports.drop 8).take 8 = (sourcePorts.drop 8).take 8 :=
  portsView8.trans (portsPiece8.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.KeccakCached.native.program encodePort 8 8))

numeric_data_binding portsView16 : (ports.drop 16).take 8 = (ports0.drop 16).take 8

numeric_data_binding portsPiece16 : (ports0.drop 16).take 8 = ((Airbender.Compiler.FunctionalNative.KeccakCached.native.program.drop 16).take 8).map encodePort

theorem portsSlice16 : (ports.drop 16).take 8 = (sourcePorts.drop 16).take 8 :=
  portsView16.trans (portsPiece16.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.KeccakCached.native.program encodePort 16 8))

numeric_data_binding portsView24 : (ports.drop 24).take 8 = (ports0.drop 24).take 8

numeric_data_binding portsPiece24 : (ports0.drop 24).take 8 = ((Airbender.Compiler.FunctionalNative.KeccakCached.native.program.drop 24).take 8).map encodePort

theorem portsSlice24 : (ports.drop 24).take 8 = (sourcePorts.drop 24).take 8 :=
  portsView24.trans (portsPiece24.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.KeccakCached.native.program encodePort 24 8))

numeric_data_binding portsView32 : (ports.drop 32).take 8 = (ports32.drop 0).take 8

numeric_data_binding portsPiece32 : (ports32.drop 0).take 8 = ((Airbender.Compiler.FunctionalNative.KeccakCached.native.program.drop 32).take 8).map encodePort

theorem portsSlice32 : (ports.drop 32).take 8 = (sourcePorts.drop 32).take 8 :=
  portsView32.trans (portsPiece32.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.KeccakCached.native.program encodePort 32 8))

numeric_data_binding portsView40 : (ports.drop 40).take 8 = (ports32.drop 8).take 8

numeric_data_binding portsPiece40 : (ports32.drop 8).take 8 = ((Airbender.Compiler.FunctionalNative.KeccakCached.native.program.drop 40).take 8).map encodePort

theorem portsSlice40 : (ports.drop 40).take 8 = (sourcePorts.drop 40).take 8 :=
  portsView40.trans (portsPiece40.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.KeccakCached.native.program encodePort 40 8))

numeric_data_binding portsView48 : (ports.drop 48).take 8 = (ports32.drop 16).take 8

numeric_data_binding portsPiece48 : (ports32.drop 16).take 8 = ((Airbender.Compiler.FunctionalNative.KeccakCached.native.program.drop 48).take 8).map encodePort

theorem portsSlice48 : (ports.drop 48).take 8 = (sourcePorts.drop 48).take 8 :=
  portsView48.trans (portsPiece48.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.KeccakCached.native.program encodePort 48 8))

numeric_data_binding portsView56 : (ports.drop 56).take 8 = (ports32.drop 24).take 8

numeric_data_binding portsPiece56 : (ports32.drop 24).take 8 = ((Airbender.Compiler.FunctionalNative.KeccakCached.native.program.drop 56).take 8).map encodePort

theorem portsSlice56 : (ports.drop 56).take 8 = (sourcePorts.drop 56).take 8 :=
  portsView56.trans (portsPiece56.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.KeccakCached.native.program encodePort 56 8))

numeric_data_binding portsView64 : (ports.drop 64).take 8 = (ports64.drop 0).take 8

numeric_data_binding portsPiece64 : (ports64.drop 0).take 8 = ((Airbender.Compiler.FunctionalNative.KeccakCached.native.program.drop 64).take 8).map encodePort

theorem portsSlice64 : (ports.drop 64).take 8 = (sourcePorts.drop 64).take 8 :=
  portsView64.trans (portsPiece64.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.KeccakCached.native.program encodePort 64 8))

numeric_data_binding portsView72 : (ports.drop 72).take 8 = (ports64.drop 8).take 8

numeric_data_binding portsPiece72 : (ports64.drop 8).take 8 = ((Airbender.Compiler.FunctionalNative.KeccakCached.native.program.drop 72).take 8).map encodePort

theorem portsSlice72 : (ports.drop 72).take 8 = (sourcePorts.drop 72).take 8 :=
  portsView72.trans (portsPiece72.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.KeccakCached.native.program encodePort 72 8))

numeric_data_binding portsView80 : (ports.drop 80).take 8 = (ports64.drop 16).take 8

numeric_data_binding portsPiece80 : (ports64.drop 16).take 8 = ((Airbender.Compiler.FunctionalNative.KeccakCached.native.program.drop 80).take 8).map encodePort

theorem portsSlice80 : (ports.drop 80).take 8 = (sourcePorts.drop 80).take 8 :=
  portsView80.trans (portsPiece80.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.KeccakCached.native.program encodePort 80 8))

numeric_data_binding portsView88 : (ports.drop 88).take 8 = (ports64.drop 24).take 8

numeric_data_binding portsPiece88 : (ports64.drop 24).take 8 = ((Airbender.Compiler.FunctionalNative.KeccakCached.native.program.drop 88).take 8).map encodePort

theorem portsSlice88 : (ports.drop 88).take 8 = (sourcePorts.drop 88).take 8 :=
  portsView88.trans (portsPiece88.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.KeccakCached.native.program encodePort 88 8))

numeric_data_binding portsView96 : (ports.drop 96).take 8 = (ports96.drop 0).take 8

numeric_data_binding portsPiece96 : (ports96.drop 0).take 8 = ((Airbender.Compiler.FunctionalNative.KeccakCached.native.program.drop 96).take 8).map encodePort

theorem portsSlice96 : (ports.drop 96).take 8 = (sourcePorts.drop 96).take 8 :=
  portsView96.trans (portsPiece96.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.KeccakCached.native.program encodePort 96 8))

numeric_data_binding portsView104 : (ports.drop 104).take 8 = (ports96.drop 8).take 8

numeric_data_binding portsPiece104 : (ports96.drop 8).take 8 = ((Airbender.Compiler.FunctionalNative.KeccakCached.native.program.drop 104).take 8).map encodePort

theorem portsSlice104 : (ports.drop 104).take 8 = (sourcePorts.drop 104).take 8 :=
  portsView104.trans (portsPiece104.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.KeccakCached.native.program encodePort 104 8))

numeric_data_binding portsView112 : (ports.drop 112).take 8 = (ports96.drop 16).take 8

numeric_data_binding portsPiece112 : (ports96.drop 16).take 8 = ((Airbender.Compiler.FunctionalNative.KeccakCached.native.program.drop 112).take 8).map encodePort

theorem portsSlice112 : (ports.drop 112).take 8 = (sourcePorts.drop 112).take 8 :=
  portsView112.trans (portsPiece112.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.KeccakCached.native.program encodePort 112 8))

numeric_data_binding portsView120 : (ports.drop 120).take 8 = (ports96.drop 24).take 8

numeric_data_binding portsPiece120 : (ports96.drop 24).take 8 = ((Airbender.Compiler.FunctionalNative.KeccakCached.native.program.drop 120).take 8).map encodePort

theorem portsSlice120 : (ports.drop 120).take 8 = (sourcePorts.drop 120).take 8 :=
  portsView120.trans (portsPiece120.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.KeccakCached.native.program encodePort 120 8))

numeric_data_binding portsView128 : (ports.drop 128).take 8 = (ports128.drop 0).take 8

numeric_data_binding portsPiece128 : (ports128.drop 0).take 8 = ((Airbender.Compiler.FunctionalNative.KeccakCached.native.program.drop 128).take 8).map encodePort

theorem portsSlice128 : (ports.drop 128).take 8 = (sourcePorts.drop 128).take 8 :=
  portsView128.trans (portsPiece128.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.KeccakCached.native.program encodePort 128 8))

numeric_data_binding portsView136 : (ports.drop 136).take 8 = (ports128.drop 8).take 8

numeric_data_binding portsPiece136 : (ports128.drop 8).take 8 = ((Airbender.Compiler.FunctionalNative.KeccakCached.native.program.drop 136).take 8).map encodePort

theorem portsSlice136 : (ports.drop 136).take 8 = (sourcePorts.drop 136).take 8 :=
  portsView136.trans (portsPiece136.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.KeccakCached.native.program encodePort 136 8))

numeric_data_binding portsView144 : (ports.drop 144).take 8 = (ports128.drop 16).take 8

numeric_data_binding portsPiece144 : (ports128.drop 16).take 8 = ((Airbender.Compiler.FunctionalNative.KeccakCached.native.program.drop 144).take 8).map encodePort

theorem portsSlice144 : (ports.drop 144).take 8 = (sourcePorts.drop 144).take 8 :=
  portsView144.trans (portsPiece144.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.KeccakCached.native.program encodePort 144 8))

numeric_data_binding portsView152 : (ports.drop 152).take 8 = (ports128.drop 24).take 8

numeric_data_binding portsPiece152 : (ports128.drop 24).take 8 = ((Airbender.Compiler.FunctionalNative.KeccakCached.native.program.drop 152).take 8).map encodePort

theorem portsSlice152 : (ports.drop 152).take 8 = (sourcePorts.drop 152).take 8 :=
  portsView152.trans (portsPiece152.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.KeccakCached.native.program encodePort 152 8))

numeric_data_binding portsView160 : (ports.drop 160).take 8 = (ports160.drop 0).take 8

numeric_data_binding portsPiece160 : (ports160.drop 0).take 8 = ((Airbender.Compiler.FunctionalNative.KeccakCached.native.program.drop 160).take 8).map encodePort

theorem portsSlice160 : (ports.drop 160).take 8 = (sourcePorts.drop 160).take 8 :=
  portsView160.trans (portsPiece160.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.KeccakCached.native.program encodePort 160 8))

numeric_data_binding portsView168 : (ports.drop 168).take 8 = (ports160.drop 8).take 8

numeric_data_binding portsPiece168 : (ports160.drop 8).take 8 = ((Airbender.Compiler.FunctionalNative.KeccakCached.native.program.drop 168).take 8).map encodePort

theorem portsSlice168 : (ports.drop 168).take 8 = (sourcePorts.drop 168).take 8 :=
  portsView168.trans (portsPiece168.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.KeccakCached.native.program encodePort 168 8))

numeric_data_binding portsView176 : (ports.drop 176).take 8 = (ports160.drop 16).take 8

numeric_data_binding portsPiece176 : (ports160.drop 16).take 8 = ((Airbender.Compiler.FunctionalNative.KeccakCached.native.program.drop 176).take 8).map encodePort

theorem portsSlice176 : (ports.drop 176).take 8 = (sourcePorts.drop 176).take 8 :=
  portsView176.trans (portsPiece176.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.KeccakCached.native.program encodePort 176 8))

numeric_data_binding portsView184 : (ports.drop 184).take 1 = (ports160.drop 24).take 1

numeric_data_binding portsPiece184 : (ports160.drop 24).take 1 = ((Airbender.Compiler.FunctionalNative.KeccakCached.native.program.drop 184).take 1).map encodePort

theorem portsSlice184 : (ports.drop 184).take 1 = (sourcePorts.drop 184).take 1 :=
  portsView184.trans (portsPiece184.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.KeccakCached.native.program encodePort 184 1))

theorem portsNode8_16 : (ports.drop 8).take 16 = (sourcePorts.drop 8).take 16 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 8 8 8 portsSlice8 portsSlice16

theorem portsNode0_24 : (ports.drop 0).take 24 = (sourcePorts.drop 0).take 24 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 0 8 16 portsSlice0 portsNode8_16

theorem portsNode32_16 : (ports.drop 32).take 16 = (sourcePorts.drop 32).take 16 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 32 8 8 portsSlice32 portsSlice40

theorem portsNode24_24 : (ports.drop 24).take 24 = (sourcePorts.drop 24).take 24 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 24 8 16 portsSlice24 portsNode32_16

theorem portsNode0_48 : (ports.drop 0).take 48 = (sourcePorts.drop 0).take 48 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 0 24 24 portsNode0_24 portsNode24_24

theorem portsNode56_16 : (ports.drop 56).take 16 = (sourcePorts.drop 56).take 16 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 56 8 8 portsSlice56 portsSlice64

theorem portsNode48_24 : (ports.drop 48).take 24 = (sourcePorts.drop 48).take 24 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 48 8 16 portsSlice48 portsNode56_16

theorem portsNode80_16 : (ports.drop 80).take 16 = (sourcePorts.drop 80).take 16 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 80 8 8 portsSlice80 portsSlice88

theorem portsNode72_24 : (ports.drop 72).take 24 = (sourcePorts.drop 72).take 24 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 72 8 16 portsSlice72 portsNode80_16

theorem portsNode48_48 : (ports.drop 48).take 48 = (sourcePorts.drop 48).take 48 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 48 24 24 portsNode48_24 portsNode72_24

theorem portsNode0_96 : (ports.drop 0).take 96 = (sourcePorts.drop 0).take 96 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 0 48 48 portsNode0_48 portsNode48_48

theorem portsNode104_16 : (ports.drop 104).take 16 = (sourcePorts.drop 104).take 16 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 104 8 8 portsSlice104 portsSlice112

theorem portsNode96_24 : (ports.drop 96).take 24 = (sourcePorts.drop 96).take 24 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 96 8 16 portsSlice96 portsNode104_16

theorem portsNode128_16 : (ports.drop 128).take 16 = (sourcePorts.drop 128).take 16 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 128 8 8 portsSlice128 portsSlice136

theorem portsNode120_24 : (ports.drop 120).take 24 = (sourcePorts.drop 120).take 24 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 120 8 16 portsSlice120 portsNode128_16

theorem portsNode96_48 : (ports.drop 96).take 48 = (sourcePorts.drop 96).take 48 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 96 24 24 portsNode96_24 portsNode120_24

theorem portsNode152_16 : (ports.drop 152).take 16 = (sourcePorts.drop 152).take 16 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 152 8 8 portsSlice152 portsSlice160

theorem portsNode144_24 : (ports.drop 144).take 24 = (sourcePorts.drop 144).take 24 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 144 8 16 portsSlice144 portsNode152_16

theorem portsNode176_9 : (ports.drop 176).take 9 = (sourcePorts.drop 176).take 9 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 176 8 1 portsSlice176 portsSlice184

theorem portsNode168_17 : (ports.drop 168).take 17 = (sourcePorts.drop 168).take 17 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 168 8 9 portsSlice168 portsNode176_9

theorem portsNode144_41 : (ports.drop 144).take 41 = (sourcePorts.drop 144).take 41 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 144 24 17 portsNode144_24 portsNode168_17

theorem portsNode96_89 : (ports.drop 96).take 89 = (sourcePorts.drop 96).take 89 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 96 48 41 portsNode96_48 portsNode144_41

theorem portsNode0_185 : (ports.drop 0).take 185 = (sourcePorts.drop 0).take 185 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 0 96 89 portsNode0_96 portsNode96_89

theorem programLength : Airbender.Compiler.FunctionalNative.KeccakCached.native.program.length = 185 := by decide +kernel

theorem ports_binding : ports = sourcePorts :=
  NumericQueryFrameChecks.complete_binding ports sourcePorts 185
    (by decide +kernel) (by rw [sourcePorts, List.length_map, programLength]) portsNode0_185

end Airbender.Compiler.FunctionalStepChecks.KeccakCached
