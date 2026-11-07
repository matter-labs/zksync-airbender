import Airbender.Proofs.GKRProtocol.FunctionalStepChecks.BigintCached.Data
import Airbender.Proofs.GKRProtocol.FunctionalNative.BigintCachedFoundation
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.FunctionalStepChecks.BigintCached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def encodePort (step : FunctionalStep) := NumericFunctionalStepChecks.encode Airbender.Compiler.FunctionalNative.BigintCached.native.isBase ([], step)

noncomputable def sourcePorts := Airbender.Compiler.FunctionalNative.BigintCached.native.program.map encodePort

numeric_data_binding portsView0 : (ports.drop 0).take 8 = (ports0.drop 0).take 8

numeric_data_binding portsPiece0 : (ports0.drop 0).take 8 = ((Airbender.Compiler.FunctionalNative.BigintCached.native.program.drop 0).take 8).map encodePort

theorem portsSlice0 : (ports.drop 0).take 8 = (sourcePorts.drop 0).take 8 :=
  portsView0.trans (portsPiece0.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BigintCached.native.program encodePort 0 8))

numeric_data_binding portsView8 : (ports.drop 8).take 8 = (ports0.drop 8).take 8

numeric_data_binding portsPiece8 : (ports0.drop 8).take 8 = ((Airbender.Compiler.FunctionalNative.BigintCached.native.program.drop 8).take 8).map encodePort

theorem portsSlice8 : (ports.drop 8).take 8 = (sourcePorts.drop 8).take 8 :=
  portsView8.trans (portsPiece8.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BigintCached.native.program encodePort 8 8))

numeric_data_binding portsView16 : (ports.drop 16).take 8 = (ports0.drop 16).take 8

numeric_data_binding portsPiece16 : (ports0.drop 16).take 8 = ((Airbender.Compiler.FunctionalNative.BigintCached.native.program.drop 16).take 8).map encodePort

theorem portsSlice16 : (ports.drop 16).take 8 = (sourcePorts.drop 16).take 8 :=
  portsView16.trans (portsPiece16.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BigintCached.native.program encodePort 16 8))

numeric_data_binding portsView24 : (ports.drop 24).take 8 = (ports0.drop 24).take 8

numeric_data_binding portsPiece24 : (ports0.drop 24).take 8 = ((Airbender.Compiler.FunctionalNative.BigintCached.native.program.drop 24).take 8).map encodePort

theorem portsSlice24 : (ports.drop 24).take 8 = (sourcePorts.drop 24).take 8 :=
  portsView24.trans (portsPiece24.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BigintCached.native.program encodePort 24 8))

numeric_data_binding portsView32 : (ports.drop 32).take 8 = (ports32.drop 0).take 8

numeric_data_binding portsPiece32 : (ports32.drop 0).take 8 = ((Airbender.Compiler.FunctionalNative.BigintCached.native.program.drop 32).take 8).map encodePort

theorem portsSlice32 : (ports.drop 32).take 8 = (sourcePorts.drop 32).take 8 :=
  portsView32.trans (portsPiece32.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BigintCached.native.program encodePort 32 8))

numeric_data_binding portsView40 : (ports.drop 40).take 8 = (ports32.drop 8).take 8

numeric_data_binding portsPiece40 : (ports32.drop 8).take 8 = ((Airbender.Compiler.FunctionalNative.BigintCached.native.program.drop 40).take 8).map encodePort

theorem portsSlice40 : (ports.drop 40).take 8 = (sourcePorts.drop 40).take 8 :=
  portsView40.trans (portsPiece40.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BigintCached.native.program encodePort 40 8))

numeric_data_binding portsView48 : (ports.drop 48).take 8 = (ports32.drop 16).take 8

numeric_data_binding portsPiece48 : (ports32.drop 16).take 8 = ((Airbender.Compiler.FunctionalNative.BigintCached.native.program.drop 48).take 8).map encodePort

theorem portsSlice48 : (ports.drop 48).take 8 = (sourcePorts.drop 48).take 8 :=
  portsView48.trans (portsPiece48.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BigintCached.native.program encodePort 48 8))

numeric_data_binding portsView56 : (ports.drop 56).take 8 = (ports32.drop 24).take 8

numeric_data_binding portsPiece56 : (ports32.drop 24).take 8 = ((Airbender.Compiler.FunctionalNative.BigintCached.native.program.drop 56).take 8).map encodePort

theorem portsSlice56 : (ports.drop 56).take 8 = (sourcePorts.drop 56).take 8 :=
  portsView56.trans (portsPiece56.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BigintCached.native.program encodePort 56 8))

numeric_data_binding portsView64 : (ports.drop 64).take 8 = (ports64.drop 0).take 8

numeric_data_binding portsPiece64 : (ports64.drop 0).take 8 = ((Airbender.Compiler.FunctionalNative.BigintCached.native.program.drop 64).take 8).map encodePort

theorem portsSlice64 : (ports.drop 64).take 8 = (sourcePorts.drop 64).take 8 :=
  portsView64.trans (portsPiece64.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BigintCached.native.program encodePort 64 8))

numeric_data_binding portsView72 : (ports.drop 72).take 8 = (ports64.drop 8).take 8

numeric_data_binding portsPiece72 : (ports64.drop 8).take 8 = ((Airbender.Compiler.FunctionalNative.BigintCached.native.program.drop 72).take 8).map encodePort

theorem portsSlice72 : (ports.drop 72).take 8 = (sourcePorts.drop 72).take 8 :=
  portsView72.trans (portsPiece72.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BigintCached.native.program encodePort 72 8))

numeric_data_binding portsView80 : (ports.drop 80).take 8 = (ports64.drop 16).take 8

numeric_data_binding portsPiece80 : (ports64.drop 16).take 8 = ((Airbender.Compiler.FunctionalNative.BigintCached.native.program.drop 80).take 8).map encodePort

theorem portsSlice80 : (ports.drop 80).take 8 = (sourcePorts.drop 80).take 8 :=
  portsView80.trans (portsPiece80.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BigintCached.native.program encodePort 80 8))

numeric_data_binding portsView88 : (ports.drop 88).take 8 = (ports64.drop 24).take 8

numeric_data_binding portsPiece88 : (ports64.drop 24).take 8 = ((Airbender.Compiler.FunctionalNative.BigintCached.native.program.drop 88).take 8).map encodePort

theorem portsSlice88 : (ports.drop 88).take 8 = (sourcePorts.drop 88).take 8 :=
  portsView88.trans (portsPiece88.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BigintCached.native.program encodePort 88 8))

numeric_data_binding portsView96 : (ports.drop 96).take 8 = (ports96.drop 0).take 8

numeric_data_binding portsPiece96 : (ports96.drop 0).take 8 = ((Airbender.Compiler.FunctionalNative.BigintCached.native.program.drop 96).take 8).map encodePort

theorem portsSlice96 : (ports.drop 96).take 8 = (sourcePorts.drop 96).take 8 :=
  portsView96.trans (portsPiece96.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BigintCached.native.program encodePort 96 8))

numeric_data_binding portsView104 : (ports.drop 104).take 8 = (ports96.drop 8).take 8

numeric_data_binding portsPiece104 : (ports96.drop 8).take 8 = ((Airbender.Compiler.FunctionalNative.BigintCached.native.program.drop 104).take 8).map encodePort

theorem portsSlice104 : (ports.drop 104).take 8 = (sourcePorts.drop 104).take 8 :=
  portsView104.trans (portsPiece104.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BigintCached.native.program encodePort 104 8))

numeric_data_binding portsView112 : (ports.drop 112).take 8 = (ports96.drop 16).take 8

numeric_data_binding portsPiece112 : (ports96.drop 16).take 8 = ((Airbender.Compiler.FunctionalNative.BigintCached.native.program.drop 112).take 8).map encodePort

theorem portsSlice112 : (ports.drop 112).take 8 = (sourcePorts.drop 112).take 8 :=
  portsView112.trans (portsPiece112.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BigintCached.native.program encodePort 112 8))

numeric_data_binding portsView120 : (ports.drop 120).take 8 = (ports96.drop 24).take 8

numeric_data_binding portsPiece120 : (ports96.drop 24).take 8 = ((Airbender.Compiler.FunctionalNative.BigintCached.native.program.drop 120).take 8).map encodePort

theorem portsSlice120 : (ports.drop 120).take 8 = (sourcePorts.drop 120).take 8 :=
  portsView120.trans (portsPiece120.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BigintCached.native.program encodePort 120 8))

numeric_data_binding portsView128 : (ports.drop 128).take 8 = (ports128.drop 0).take 8

numeric_data_binding portsPiece128 : (ports128.drop 0).take 8 = ((Airbender.Compiler.FunctionalNative.BigintCached.native.program.drop 128).take 8).map encodePort

theorem portsSlice128 : (ports.drop 128).take 8 = (sourcePorts.drop 128).take 8 :=
  portsView128.trans (portsPiece128.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BigintCached.native.program encodePort 128 8))

numeric_data_binding portsView136 : (ports.drop 136).take 8 = (ports128.drop 8).take 8

numeric_data_binding portsPiece136 : (ports128.drop 8).take 8 = ((Airbender.Compiler.FunctionalNative.BigintCached.native.program.drop 136).take 8).map encodePort

theorem portsSlice136 : (ports.drop 136).take 8 = (sourcePorts.drop 136).take 8 :=
  portsView136.trans (portsPiece136.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BigintCached.native.program encodePort 136 8))

numeric_data_binding portsView144 : (ports.drop 144).take 8 = (ports128.drop 16).take 8

numeric_data_binding portsPiece144 : (ports128.drop 16).take 8 = ((Airbender.Compiler.FunctionalNative.BigintCached.native.program.drop 144).take 8).map encodePort

theorem portsSlice144 : (ports.drop 144).take 8 = (sourcePorts.drop 144).take 8 :=
  portsView144.trans (portsPiece144.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BigintCached.native.program encodePort 144 8))

numeric_data_binding portsView152 : (ports.drop 152).take 8 = (ports128.drop 24).take 8

numeric_data_binding portsPiece152 : (ports128.drop 24).take 8 = ((Airbender.Compiler.FunctionalNative.BigintCached.native.program.drop 152).take 8).map encodePort

theorem portsSlice152 : (ports.drop 152).take 8 = (sourcePorts.drop 152).take 8 :=
  portsView152.trans (portsPiece152.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BigintCached.native.program encodePort 152 8))

numeric_data_binding portsView160 : (ports.drop 160).take 8 = (ports160.drop 0).take 8

numeric_data_binding portsPiece160 : (ports160.drop 0).take 8 = ((Airbender.Compiler.FunctionalNative.BigintCached.native.program.drop 160).take 8).map encodePort

theorem portsSlice160 : (ports.drop 160).take 8 = (sourcePorts.drop 160).take 8 :=
  portsView160.trans (portsPiece160.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BigintCached.native.program encodePort 160 8))

numeric_data_binding portsView168 : (ports.drop 168).take 8 = (ports160.drop 8).take 8

numeric_data_binding portsPiece168 : (ports160.drop 8).take 8 = ((Airbender.Compiler.FunctionalNative.BigintCached.native.program.drop 168).take 8).map encodePort

theorem portsSlice168 : (ports.drop 168).take 8 = (sourcePorts.drop 168).take 8 :=
  portsView168.trans (portsPiece168.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BigintCached.native.program encodePort 168 8))

numeric_data_binding portsView176 : (ports.drop 176).take 8 = (ports160.drop 16).take 8

numeric_data_binding portsPiece176 : (ports160.drop 16).take 8 = ((Airbender.Compiler.FunctionalNative.BigintCached.native.program.drop 176).take 8).map encodePort

theorem portsSlice176 : (ports.drop 176).take 8 = (sourcePorts.drop 176).take 8 :=
  portsView176.trans (portsPiece176.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BigintCached.native.program encodePort 176 8))

numeric_data_binding portsView184 : (ports.drop 184).take 8 = (ports160.drop 24).take 8

numeric_data_binding portsPiece184 : (ports160.drop 24).take 8 = ((Airbender.Compiler.FunctionalNative.BigintCached.native.program.drop 184).take 8).map encodePort

theorem portsSlice184 : (ports.drop 184).take 8 = (sourcePorts.drop 184).take 8 :=
  portsView184.trans (portsPiece184.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BigintCached.native.program encodePort 184 8))

numeric_data_binding portsView192 : (ports.drop 192).take 8 = (ports192.drop 0).take 8

numeric_data_binding portsPiece192 : (ports192.drop 0).take 8 = ((Airbender.Compiler.FunctionalNative.BigintCached.native.program.drop 192).take 8).map encodePort

theorem portsSlice192 : (ports.drop 192).take 8 = (sourcePorts.drop 192).take 8 :=
  portsView192.trans (portsPiece192.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BigintCached.native.program encodePort 192 8))

numeric_data_binding portsView200 : (ports.drop 200).take 8 = (ports192.drop 8).take 8

numeric_data_binding portsPiece200 : (ports192.drop 8).take 8 = ((Airbender.Compiler.FunctionalNative.BigintCached.native.program.drop 200).take 8).map encodePort

theorem portsSlice200 : (ports.drop 200).take 8 = (sourcePorts.drop 200).take 8 :=
  portsView200.trans (portsPiece200.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BigintCached.native.program encodePort 200 8))

numeric_data_binding portsView208 : (ports.drop 208).take 8 = (ports192.drop 16).take 8

numeric_data_binding portsPiece208 : (ports192.drop 16).take 8 = ((Airbender.Compiler.FunctionalNative.BigintCached.native.program.drop 208).take 8).map encodePort

theorem portsSlice208 : (ports.drop 208).take 8 = (sourcePorts.drop 208).take 8 :=
  portsView208.trans (portsPiece208.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BigintCached.native.program encodePort 208 8))

numeric_data_binding portsView216 : (ports.drop 216).take 8 = (ports192.drop 24).take 8

numeric_data_binding portsPiece216 : (ports192.drop 24).take 8 = ((Airbender.Compiler.FunctionalNative.BigintCached.native.program.drop 216).take 8).map encodePort

theorem portsSlice216 : (ports.drop 216).take 8 = (sourcePorts.drop 216).take 8 :=
  portsView216.trans (portsPiece216.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BigintCached.native.program encodePort 216 8))

numeric_data_binding portsView224 : (ports.drop 224).take 8 = (ports224.drop 0).take 8

numeric_data_binding portsPiece224 : (ports224.drop 0).take 8 = ((Airbender.Compiler.FunctionalNative.BigintCached.native.program.drop 224).take 8).map encodePort

theorem portsSlice224 : (ports.drop 224).take 8 = (sourcePorts.drop 224).take 8 :=
  portsView224.trans (portsPiece224.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BigintCached.native.program encodePort 224 8))

numeric_data_binding portsView232 : (ports.drop 232).take 8 = (ports224.drop 8).take 8

numeric_data_binding portsPiece232 : (ports224.drop 8).take 8 = ((Airbender.Compiler.FunctionalNative.BigintCached.native.program.drop 232).take 8).map encodePort

theorem portsSlice232 : (ports.drop 232).take 8 = (sourcePorts.drop 232).take 8 :=
  portsView232.trans (portsPiece232.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BigintCached.native.program encodePort 232 8))

numeric_data_binding portsView240 : (ports.drop 240).take 8 = (ports224.drop 16).take 8

numeric_data_binding portsPiece240 : (ports224.drop 16).take 8 = ((Airbender.Compiler.FunctionalNative.BigintCached.native.program.drop 240).take 8).map encodePort

theorem portsSlice240 : (ports.drop 240).take 8 = (sourcePorts.drop 240).take 8 :=
  portsView240.trans (portsPiece240.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BigintCached.native.program encodePort 240 8))

numeric_data_binding portsView248 : (ports.drop 248).take 8 = (ports224.drop 24).take 8

numeric_data_binding portsPiece248 : (ports224.drop 24).take 8 = ((Airbender.Compiler.FunctionalNative.BigintCached.native.program.drop 248).take 8).map encodePort

theorem portsSlice248 : (ports.drop 248).take 8 = (sourcePorts.drop 248).take 8 :=
  portsView248.trans (portsPiece248.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BigintCached.native.program encodePort 248 8))

numeric_data_binding portsView256 : (ports.drop 256).take 8 = (ports256.drop 0).take 8

numeric_data_binding portsPiece256 : (ports256.drop 0).take 8 = ((Airbender.Compiler.FunctionalNative.BigintCached.native.program.drop 256).take 8).map encodePort

theorem portsSlice256 : (ports.drop 256).take 8 = (sourcePorts.drop 256).take 8 :=
  portsView256.trans (portsPiece256.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BigintCached.native.program encodePort 256 8))

numeric_data_binding portsView264 : (ports.drop 264).take 8 = (ports256.drop 8).take 8

numeric_data_binding portsPiece264 : (ports256.drop 8).take 8 = ((Airbender.Compiler.FunctionalNative.BigintCached.native.program.drop 264).take 8).map encodePort

theorem portsSlice264 : (ports.drop 264).take 8 = (sourcePorts.drop 264).take 8 :=
  portsView264.trans (portsPiece264.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BigintCached.native.program encodePort 264 8))

numeric_data_binding portsView272 : (ports.drop 272).take 8 = (ports256.drop 16).take 8

numeric_data_binding portsPiece272 : (ports256.drop 16).take 8 = ((Airbender.Compiler.FunctionalNative.BigintCached.native.program.drop 272).take 8).map encodePort

theorem portsSlice272 : (ports.drop 272).take 8 = (sourcePorts.drop 272).take 8 :=
  portsView272.trans (portsPiece272.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BigintCached.native.program encodePort 272 8))

numeric_data_binding portsView280 : (ports.drop 280).take 8 = (ports256.drop 24).take 8

numeric_data_binding portsPiece280 : (ports256.drop 24).take 8 = ((Airbender.Compiler.FunctionalNative.BigintCached.native.program.drop 280).take 8).map encodePort

theorem portsSlice280 : (ports.drop 280).take 8 = (sourcePorts.drop 280).take 8 :=
  portsView280.trans (portsPiece280.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BigintCached.native.program encodePort 280 8))

numeric_data_binding portsView288 : (ports.drop 288).take 6 = (ports288.drop 0).take 6

numeric_data_binding portsPiece288 : (ports288.drop 0).take 6 = ((Airbender.Compiler.FunctionalNative.BigintCached.native.program.drop 288).take 6).map encodePort

theorem portsSlice288 : (ports.drop 288).take 6 = (sourcePorts.drop 288).take 6 :=
  portsView288.trans (portsPiece288.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BigintCached.native.program encodePort 288 6))

theorem portsNode0_16 : (ports.drop 0).take 16 = (sourcePorts.drop 0).take 16 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 0 8 8 portsSlice0 portsSlice8

theorem portsNode16_16 : (ports.drop 16).take 16 = (sourcePorts.drop 16).take 16 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 16 8 8 portsSlice16 portsSlice24

theorem portsNode0_32 : (ports.drop 0).take 32 = (sourcePorts.drop 0).take 32 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 0 16 16 portsNode0_16 portsNode16_16

theorem portsNode32_16 : (ports.drop 32).take 16 = (sourcePorts.drop 32).take 16 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 32 8 8 portsSlice32 portsSlice40

theorem portsNode56_16 : (ports.drop 56).take 16 = (sourcePorts.drop 56).take 16 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 56 8 8 portsSlice56 portsSlice64

theorem portsNode48_24 : (ports.drop 48).take 24 = (sourcePorts.drop 48).take 24 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 48 8 16 portsSlice48 portsNode56_16

theorem portsNode32_40 : (ports.drop 32).take 40 = (sourcePorts.drop 32).take 40 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 32 16 24 portsNode32_16 portsNode48_24

theorem portsNode0_72 : (ports.drop 0).take 72 = (sourcePorts.drop 0).take 72 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 0 32 40 portsNode0_32 portsNode32_40

theorem portsNode72_16 : (ports.drop 72).take 16 = (sourcePorts.drop 72).take 16 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 72 8 8 portsSlice72 portsSlice80

theorem portsNode88_16 : (ports.drop 88).take 16 = (sourcePorts.drop 88).take 16 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 88 8 8 portsSlice88 portsSlice96

theorem portsNode72_32 : (ports.drop 72).take 32 = (sourcePorts.drop 72).take 32 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 72 16 16 portsNode72_16 portsNode88_16

theorem portsNode104_16 : (ports.drop 104).take 16 = (sourcePorts.drop 104).take 16 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 104 8 8 portsSlice104 portsSlice112

theorem portsNode128_16 : (ports.drop 128).take 16 = (sourcePorts.drop 128).take 16 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 128 8 8 portsSlice128 portsSlice136

theorem portsNode120_24 : (ports.drop 120).take 24 = (sourcePorts.drop 120).take 24 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 120 8 16 portsSlice120 portsNode128_16

theorem portsNode104_40 : (ports.drop 104).take 40 = (sourcePorts.drop 104).take 40 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 104 16 24 portsNode104_16 portsNode120_24

theorem portsNode72_72 : (ports.drop 72).take 72 = (sourcePorts.drop 72).take 72 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 72 32 40 portsNode72_32 portsNode104_40

theorem portsNode0_144 : (ports.drop 0).take 144 = (sourcePorts.drop 0).take 144 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 0 72 72 portsNode0_72 portsNode72_72

theorem portsNode144_16 : (ports.drop 144).take 16 = (sourcePorts.drop 144).take 16 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 144 8 8 portsSlice144 portsSlice152

theorem portsNode160_16 : (ports.drop 160).take 16 = (sourcePorts.drop 160).take 16 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 160 8 8 portsSlice160 portsSlice168

theorem portsNode144_32 : (ports.drop 144).take 32 = (sourcePorts.drop 144).take 32 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 144 16 16 portsNode144_16 portsNode160_16

theorem portsNode176_16 : (ports.drop 176).take 16 = (sourcePorts.drop 176).take 16 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 176 8 8 portsSlice176 portsSlice184

theorem portsNode200_16 : (ports.drop 200).take 16 = (sourcePorts.drop 200).take 16 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 200 8 8 portsSlice200 portsSlice208

theorem portsNode192_24 : (ports.drop 192).take 24 = (sourcePorts.drop 192).take 24 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 192 8 16 portsSlice192 portsNode200_16

theorem portsNode176_40 : (ports.drop 176).take 40 = (sourcePorts.drop 176).take 40 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 176 16 24 portsNode176_16 portsNode192_24

theorem portsNode144_72 : (ports.drop 144).take 72 = (sourcePorts.drop 144).take 72 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 144 32 40 portsNode144_32 portsNode176_40

theorem portsNode216_16 : (ports.drop 216).take 16 = (sourcePorts.drop 216).take 16 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 216 8 8 portsSlice216 portsSlice224

theorem portsNode240_16 : (ports.drop 240).take 16 = (sourcePorts.drop 240).take 16 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 240 8 8 portsSlice240 portsSlice248

theorem portsNode232_24 : (ports.drop 232).take 24 = (sourcePorts.drop 232).take 24 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 232 8 16 portsSlice232 portsNode240_16

theorem portsNode216_40 : (ports.drop 216).take 40 = (sourcePorts.drop 216).take 40 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 216 16 24 portsNode216_16 portsNode232_24

theorem portsNode256_16 : (ports.drop 256).take 16 = (sourcePorts.drop 256).take 16 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 256 8 8 portsSlice256 portsSlice264

theorem portsNode280_14 : (ports.drop 280).take 14 = (sourcePorts.drop 280).take 14 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 280 8 6 portsSlice280 portsSlice288

theorem portsNode272_22 : (ports.drop 272).take 22 = (sourcePorts.drop 272).take 22 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 272 8 14 portsSlice272 portsNode280_14

theorem portsNode256_38 : (ports.drop 256).take 38 = (sourcePorts.drop 256).take 38 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 256 16 22 portsNode256_16 portsNode272_22

theorem portsNode216_78 : (ports.drop 216).take 78 = (sourcePorts.drop 216).take 78 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 216 40 38 portsNode216_40 portsNode256_38

theorem portsNode144_150 : (ports.drop 144).take 150 = (sourcePorts.drop 144).take 150 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 144 72 78 portsNode144_72 portsNode216_78

theorem portsNode0_294 : (ports.drop 0).take 294 = (sourcePorts.drop 0).take 294 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 0 144 150 portsNode0_144 portsNode144_150

theorem programLength : Airbender.Compiler.FunctionalNative.BigintCached.native.program.length = 294 := by decide +kernel

theorem ports_binding : ports = sourcePorts :=
  NumericQueryFrameChecks.complete_binding ports sourcePorts 294
    (by decide +kernel) (by rw [sourcePorts, List.length_map, programLength]) portsNode0_294

end Airbender.Compiler.FunctionalStepChecks.BigintCached
