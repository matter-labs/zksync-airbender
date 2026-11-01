import Airbender.Proofs.GKRProtocol.FunctionalStepChecks.BlakeRoundCached.Data
import Airbender.Proofs.GKRProtocol.FunctionalNative.BlakeRoundCachedFoundation
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.FunctionalStepChecks.BlakeRoundCached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def encodePort (step : FunctionalStep) := NumericFunctionalStepChecks.encode Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.isBase ([], step)

noncomputable def sourcePorts := Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program.map encodePort

numeric_data_binding portsView0 : (ports.drop 0).take 8 = (ports0.drop 0).take 8

numeric_data_binding portsPiece0 : (ports0.drop 0).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program.drop 0).take 8).map encodePort

theorem portsSlice0 : (ports.drop 0).take 8 = (sourcePorts.drop 0).take 8 :=
  portsView0.trans (portsPiece0.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program encodePort 0 8))

numeric_data_binding portsView8 : (ports.drop 8).take 8 = (ports0.drop 8).take 8

numeric_data_binding portsPiece8 : (ports0.drop 8).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program.drop 8).take 8).map encodePort

theorem portsSlice8 : (ports.drop 8).take 8 = (sourcePorts.drop 8).take 8 :=
  portsView8.trans (portsPiece8.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program encodePort 8 8))

numeric_data_binding portsView16 : (ports.drop 16).take 8 = (ports0.drop 16).take 8

numeric_data_binding portsPiece16 : (ports0.drop 16).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program.drop 16).take 8).map encodePort

theorem portsSlice16 : (ports.drop 16).take 8 = (sourcePorts.drop 16).take 8 :=
  portsView16.trans (portsPiece16.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program encodePort 16 8))

numeric_data_binding portsView24 : (ports.drop 24).take 8 = (ports0.drop 24).take 8

numeric_data_binding portsPiece24 : (ports0.drop 24).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program.drop 24).take 8).map encodePort

theorem portsSlice24 : (ports.drop 24).take 8 = (sourcePorts.drop 24).take 8 :=
  portsView24.trans (portsPiece24.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program encodePort 24 8))

numeric_data_binding portsView32 : (ports.drop 32).take 8 = (ports32.drop 0).take 8

numeric_data_binding portsPiece32 : (ports32.drop 0).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program.drop 32).take 8).map encodePort

theorem portsSlice32 : (ports.drop 32).take 8 = (sourcePorts.drop 32).take 8 :=
  portsView32.trans (portsPiece32.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program encodePort 32 8))

numeric_data_binding portsView40 : (ports.drop 40).take 8 = (ports32.drop 8).take 8

numeric_data_binding portsPiece40 : (ports32.drop 8).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program.drop 40).take 8).map encodePort

theorem portsSlice40 : (ports.drop 40).take 8 = (sourcePorts.drop 40).take 8 :=
  portsView40.trans (portsPiece40.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program encodePort 40 8))

numeric_data_binding portsView48 : (ports.drop 48).take 8 = (ports32.drop 16).take 8

numeric_data_binding portsPiece48 : (ports32.drop 16).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program.drop 48).take 8).map encodePort

theorem portsSlice48 : (ports.drop 48).take 8 = (sourcePorts.drop 48).take 8 :=
  portsView48.trans (portsPiece48.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program encodePort 48 8))

numeric_data_binding portsView56 : (ports.drop 56).take 8 = (ports32.drop 24).take 8

numeric_data_binding portsPiece56 : (ports32.drop 24).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program.drop 56).take 8).map encodePort

theorem portsSlice56 : (ports.drop 56).take 8 = (sourcePorts.drop 56).take 8 :=
  portsView56.trans (portsPiece56.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program encodePort 56 8))

numeric_data_binding portsView64 : (ports.drop 64).take 8 = (ports64.drop 0).take 8

numeric_data_binding portsPiece64 : (ports64.drop 0).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program.drop 64).take 8).map encodePort

theorem portsSlice64 : (ports.drop 64).take 8 = (sourcePorts.drop 64).take 8 :=
  portsView64.trans (portsPiece64.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program encodePort 64 8))

numeric_data_binding portsView72 : (ports.drop 72).take 8 = (ports64.drop 8).take 8

numeric_data_binding portsPiece72 : (ports64.drop 8).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program.drop 72).take 8).map encodePort

theorem portsSlice72 : (ports.drop 72).take 8 = (sourcePorts.drop 72).take 8 :=
  portsView72.trans (portsPiece72.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program encodePort 72 8))

numeric_data_binding portsView80 : (ports.drop 80).take 8 = (ports64.drop 16).take 8

numeric_data_binding portsPiece80 : (ports64.drop 16).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program.drop 80).take 8).map encodePort

theorem portsSlice80 : (ports.drop 80).take 8 = (sourcePorts.drop 80).take 8 :=
  portsView80.trans (portsPiece80.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program encodePort 80 8))

numeric_data_binding portsView88 : (ports.drop 88).take 8 = (ports64.drop 24).take 8

numeric_data_binding portsPiece88 : (ports64.drop 24).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program.drop 88).take 8).map encodePort

theorem portsSlice88 : (ports.drop 88).take 8 = (sourcePorts.drop 88).take 8 :=
  portsView88.trans (portsPiece88.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program encodePort 88 8))

numeric_data_binding portsView96 : (ports.drop 96).take 8 = (ports96.drop 0).take 8

numeric_data_binding portsPiece96 : (ports96.drop 0).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program.drop 96).take 8).map encodePort

theorem portsSlice96 : (ports.drop 96).take 8 = (sourcePorts.drop 96).take 8 :=
  portsView96.trans (portsPiece96.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program encodePort 96 8))

numeric_data_binding portsView104 : (ports.drop 104).take 8 = (ports96.drop 8).take 8

numeric_data_binding portsPiece104 : (ports96.drop 8).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program.drop 104).take 8).map encodePort

theorem portsSlice104 : (ports.drop 104).take 8 = (sourcePorts.drop 104).take 8 :=
  portsView104.trans (portsPiece104.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program encodePort 104 8))

numeric_data_binding portsView112 : (ports.drop 112).take 8 = (ports96.drop 16).take 8

numeric_data_binding portsPiece112 : (ports96.drop 16).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program.drop 112).take 8).map encodePort

theorem portsSlice112 : (ports.drop 112).take 8 = (sourcePorts.drop 112).take 8 :=
  portsView112.trans (portsPiece112.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program encodePort 112 8))

numeric_data_binding portsView120 : (ports.drop 120).take 8 = (ports96.drop 24).take 8

numeric_data_binding portsPiece120 : (ports96.drop 24).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program.drop 120).take 8).map encodePort

theorem portsSlice120 : (ports.drop 120).take 8 = (sourcePorts.drop 120).take 8 :=
  portsView120.trans (portsPiece120.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program encodePort 120 8))

numeric_data_binding portsView128 : (ports.drop 128).take 8 = (ports128.drop 0).take 8

numeric_data_binding portsPiece128 : (ports128.drop 0).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program.drop 128).take 8).map encodePort

theorem portsSlice128 : (ports.drop 128).take 8 = (sourcePorts.drop 128).take 8 :=
  portsView128.trans (portsPiece128.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program encodePort 128 8))

numeric_data_binding portsView136 : (ports.drop 136).take 8 = (ports128.drop 8).take 8

numeric_data_binding portsPiece136 : (ports128.drop 8).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program.drop 136).take 8).map encodePort

theorem portsSlice136 : (ports.drop 136).take 8 = (sourcePorts.drop 136).take 8 :=
  portsView136.trans (portsPiece136.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program encodePort 136 8))

numeric_data_binding portsView144 : (ports.drop 144).take 8 = (ports128.drop 16).take 8

numeric_data_binding portsPiece144 : (ports128.drop 16).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program.drop 144).take 8).map encodePort

theorem portsSlice144 : (ports.drop 144).take 8 = (sourcePorts.drop 144).take 8 :=
  portsView144.trans (portsPiece144.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program encodePort 144 8))

numeric_data_binding portsView152 : (ports.drop 152).take 8 = (ports128.drop 24).take 8

numeric_data_binding portsPiece152 : (ports128.drop 24).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program.drop 152).take 8).map encodePort

theorem portsSlice152 : (ports.drop 152).take 8 = (sourcePorts.drop 152).take 8 :=
  portsView152.trans (portsPiece152.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program encodePort 152 8))

numeric_data_binding portsView160 : (ports.drop 160).take 8 = (ports160.drop 0).take 8

numeric_data_binding portsPiece160 : (ports160.drop 0).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program.drop 160).take 8).map encodePort

theorem portsSlice160 : (ports.drop 160).take 8 = (sourcePorts.drop 160).take 8 :=
  portsView160.trans (portsPiece160.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program encodePort 160 8))

numeric_data_binding portsView168 : (ports.drop 168).take 8 = (ports160.drop 8).take 8

numeric_data_binding portsPiece168 : (ports160.drop 8).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program.drop 168).take 8).map encodePort

theorem portsSlice168 : (ports.drop 168).take 8 = (sourcePorts.drop 168).take 8 :=
  portsView168.trans (portsPiece168.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program encodePort 168 8))

numeric_data_binding portsView176 : (ports.drop 176).take 8 = (ports160.drop 16).take 8

numeric_data_binding portsPiece176 : (ports160.drop 16).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program.drop 176).take 8).map encodePort

theorem portsSlice176 : (ports.drop 176).take 8 = (sourcePorts.drop 176).take 8 :=
  portsView176.trans (portsPiece176.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program encodePort 176 8))

numeric_data_binding portsView184 : (ports.drop 184).take 8 = (ports160.drop 24).take 8

numeric_data_binding portsPiece184 : (ports160.drop 24).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program.drop 184).take 8).map encodePort

theorem portsSlice184 : (ports.drop 184).take 8 = (sourcePorts.drop 184).take 8 :=
  portsView184.trans (portsPiece184.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program encodePort 184 8))

numeric_data_binding portsView192 : (ports.drop 192).take 8 = (ports192.drop 0).take 8

numeric_data_binding portsPiece192 : (ports192.drop 0).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program.drop 192).take 8).map encodePort

theorem portsSlice192 : (ports.drop 192).take 8 = (sourcePorts.drop 192).take 8 :=
  portsView192.trans (portsPiece192.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program encodePort 192 8))

numeric_data_binding portsView200 : (ports.drop 200).take 8 = (ports192.drop 8).take 8

numeric_data_binding portsPiece200 : (ports192.drop 8).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program.drop 200).take 8).map encodePort

theorem portsSlice200 : (ports.drop 200).take 8 = (sourcePorts.drop 200).take 8 :=
  portsView200.trans (portsPiece200.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program encodePort 200 8))

numeric_data_binding portsView208 : (ports.drop 208).take 8 = (ports192.drop 16).take 8

numeric_data_binding portsPiece208 : (ports192.drop 16).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program.drop 208).take 8).map encodePort

theorem portsSlice208 : (ports.drop 208).take 8 = (sourcePorts.drop 208).take 8 :=
  portsView208.trans (portsPiece208.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program encodePort 208 8))

numeric_data_binding portsView216 : (ports.drop 216).take 8 = (ports192.drop 24).take 8

numeric_data_binding portsPiece216 : (ports192.drop 24).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program.drop 216).take 8).map encodePort

theorem portsSlice216 : (ports.drop 216).take 8 = (sourcePorts.drop 216).take 8 :=
  portsView216.trans (portsPiece216.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program encodePort 216 8))

numeric_data_binding portsView224 : (ports.drop 224).take 8 = (ports224.drop 0).take 8

numeric_data_binding portsPiece224 : (ports224.drop 0).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program.drop 224).take 8).map encodePort

theorem portsSlice224 : (ports.drop 224).take 8 = (sourcePorts.drop 224).take 8 :=
  portsView224.trans (portsPiece224.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program encodePort 224 8))

numeric_data_binding portsView232 : (ports.drop 232).take 8 = (ports224.drop 8).take 8

numeric_data_binding portsPiece232 : (ports224.drop 8).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program.drop 232).take 8).map encodePort

theorem portsSlice232 : (ports.drop 232).take 8 = (sourcePorts.drop 232).take 8 :=
  portsView232.trans (portsPiece232.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program encodePort 232 8))

numeric_data_binding portsView240 : (ports.drop 240).take 8 = (ports224.drop 16).take 8

numeric_data_binding portsPiece240 : (ports224.drop 16).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program.drop 240).take 8).map encodePort

theorem portsSlice240 : (ports.drop 240).take 8 = (sourcePorts.drop 240).take 8 :=
  portsView240.trans (portsPiece240.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program encodePort 240 8))

numeric_data_binding portsView248 : (ports.drop 248).take 8 = (ports224.drop 24).take 8

numeric_data_binding portsPiece248 : (ports224.drop 24).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program.drop 248).take 8).map encodePort

theorem portsSlice248 : (ports.drop 248).take 8 = (sourcePorts.drop 248).take 8 :=
  portsView248.trans (portsPiece248.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program encodePort 248 8))

numeric_data_binding portsView256 : (ports.drop 256).take 8 = (ports256.drop 0).take 8

numeric_data_binding portsPiece256 : (ports256.drop 0).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program.drop 256).take 8).map encodePort

theorem portsSlice256 : (ports.drop 256).take 8 = (sourcePorts.drop 256).take 8 :=
  portsView256.trans (portsPiece256.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program encodePort 256 8))

numeric_data_binding portsView264 : (ports.drop 264).take 8 = (ports256.drop 8).take 8

numeric_data_binding portsPiece264 : (ports256.drop 8).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program.drop 264).take 8).map encodePort

theorem portsSlice264 : (ports.drop 264).take 8 = (sourcePorts.drop 264).take 8 :=
  portsView264.trans (portsPiece264.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program encodePort 264 8))

numeric_data_binding portsView272 : (ports.drop 272).take 8 = (ports256.drop 16).take 8

numeric_data_binding portsPiece272 : (ports256.drop 16).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program.drop 272).take 8).map encodePort

theorem portsSlice272 : (ports.drop 272).take 8 = (sourcePorts.drop 272).take 8 :=
  portsView272.trans (portsPiece272.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program encodePort 272 8))

numeric_data_binding portsView280 : (ports.drop 280).take 8 = (ports256.drop 24).take 8

numeric_data_binding portsPiece280 : (ports256.drop 24).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program.drop 280).take 8).map encodePort

theorem portsSlice280 : (ports.drop 280).take 8 = (sourcePorts.drop 280).take 8 :=
  portsView280.trans (portsPiece280.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program encodePort 280 8))

numeric_data_binding portsView288 : (ports.drop 288).take 8 = (ports288.drop 0).take 8

numeric_data_binding portsPiece288 : (ports288.drop 0).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program.drop 288).take 8).map encodePort

theorem portsSlice288 : (ports.drop 288).take 8 = (sourcePorts.drop 288).take 8 :=
  portsView288.trans (portsPiece288.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program encodePort 288 8))

numeric_data_binding portsView296 : (ports.drop 296).take 8 = (ports288.drop 8).take 8

numeric_data_binding portsPiece296 : (ports288.drop 8).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program.drop 296).take 8).map encodePort

theorem portsSlice296 : (ports.drop 296).take 8 = (sourcePorts.drop 296).take 8 :=
  portsView296.trans (portsPiece296.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program encodePort 296 8))

numeric_data_binding portsView304 : (ports.drop 304).take 8 = (ports288.drop 16).take 8

numeric_data_binding portsPiece304 : (ports288.drop 16).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program.drop 304).take 8).map encodePort

theorem portsSlice304 : (ports.drop 304).take 8 = (sourcePorts.drop 304).take 8 :=
  portsView304.trans (portsPiece304.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program encodePort 304 8))

numeric_data_binding portsView312 : (ports.drop 312).take 8 = (ports288.drop 24).take 8

numeric_data_binding portsPiece312 : (ports288.drop 24).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program.drop 312).take 8).map encodePort

theorem portsSlice312 : (ports.drop 312).take 8 = (sourcePorts.drop 312).take 8 :=
  portsView312.trans (portsPiece312.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program encodePort 312 8))

numeric_data_binding portsView320 : (ports.drop 320).take 8 = (ports320.drop 0).take 8

numeric_data_binding portsPiece320 : (ports320.drop 0).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program.drop 320).take 8).map encodePort

theorem portsSlice320 : (ports.drop 320).take 8 = (sourcePorts.drop 320).take 8 :=
  portsView320.trans (portsPiece320.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program encodePort 320 8))

numeric_data_binding portsView328 : (ports.drop 328).take 8 = (ports320.drop 8).take 8

numeric_data_binding portsPiece328 : (ports320.drop 8).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program.drop 328).take 8).map encodePort

theorem portsSlice328 : (ports.drop 328).take 8 = (sourcePorts.drop 328).take 8 :=
  portsView328.trans (portsPiece328.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program encodePort 328 8))

numeric_data_binding portsView336 : (ports.drop 336).take 8 = (ports320.drop 16).take 8

numeric_data_binding portsPiece336 : (ports320.drop 16).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program.drop 336).take 8).map encodePort

theorem portsSlice336 : (ports.drop 336).take 8 = (sourcePorts.drop 336).take 8 :=
  portsView336.trans (portsPiece336.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program encodePort 336 8))

numeric_data_binding portsView344 : (ports.drop 344).take 8 = (ports320.drop 24).take 8

numeric_data_binding portsPiece344 : (ports320.drop 24).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program.drop 344).take 8).map encodePort

theorem portsSlice344 : (ports.drop 344).take 8 = (sourcePorts.drop 344).take 8 :=
  portsView344.trans (portsPiece344.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program encodePort 344 8))

numeric_data_binding portsView352 : (ports.drop 352).take 8 = (ports352.drop 0).take 8

numeric_data_binding portsPiece352 : (ports352.drop 0).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program.drop 352).take 8).map encodePort

theorem portsSlice352 : (ports.drop 352).take 8 = (sourcePorts.drop 352).take 8 :=
  portsView352.trans (portsPiece352.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program encodePort 352 8))

numeric_data_binding portsView360 : (ports.drop 360).take 8 = (ports352.drop 8).take 8

numeric_data_binding portsPiece360 : (ports352.drop 8).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program.drop 360).take 8).map encodePort

theorem portsSlice360 : (ports.drop 360).take 8 = (sourcePorts.drop 360).take 8 :=
  portsView360.trans (portsPiece360.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program encodePort 360 8))

numeric_data_binding portsView368 : (ports.drop 368).take 8 = (ports352.drop 16).take 8

numeric_data_binding portsPiece368 : (ports352.drop 16).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program.drop 368).take 8).map encodePort

theorem portsSlice368 : (ports.drop 368).take 8 = (sourcePorts.drop 368).take 8 :=
  portsView368.trans (portsPiece368.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program encodePort 368 8))

numeric_data_binding portsView376 : (ports.drop 376).take 8 = (ports352.drop 24).take 8

numeric_data_binding portsPiece376 : (ports352.drop 24).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program.drop 376).take 8).map encodePort

theorem portsSlice376 : (ports.drop 376).take 8 = (sourcePorts.drop 376).take 8 :=
  portsView376.trans (portsPiece376.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program encodePort 376 8))

numeric_data_binding portsView384 : (ports.drop 384).take 8 = (ports384.drop 0).take 8

numeric_data_binding portsPiece384 : (ports384.drop 0).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program.drop 384).take 8).map encodePort

theorem portsSlice384 : (ports.drop 384).take 8 = (sourcePorts.drop 384).take 8 :=
  portsView384.trans (portsPiece384.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program encodePort 384 8))

numeric_data_binding portsView392 : (ports.drop 392).take 8 = (ports384.drop 8).take 8

numeric_data_binding portsPiece392 : (ports384.drop 8).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program.drop 392).take 8).map encodePort

theorem portsSlice392 : (ports.drop 392).take 8 = (sourcePorts.drop 392).take 8 :=
  portsView392.trans (portsPiece392.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program encodePort 392 8))

numeric_data_binding portsView400 : (ports.drop 400).take 8 = (ports384.drop 16).take 8

numeric_data_binding portsPiece400 : (ports384.drop 16).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program.drop 400).take 8).map encodePort

theorem portsSlice400 : (ports.drop 400).take 8 = (sourcePorts.drop 400).take 8 :=
  portsView400.trans (portsPiece400.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program encodePort 400 8))

numeric_data_binding portsView408 : (ports.drop 408).take 8 = (ports384.drop 24).take 8

numeric_data_binding portsPiece408 : (ports384.drop 24).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program.drop 408).take 8).map encodePort

theorem portsSlice408 : (ports.drop 408).take 8 = (sourcePorts.drop 408).take 8 :=
  portsView408.trans (portsPiece408.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program encodePort 408 8))

numeric_data_binding portsView416 : (ports.drop 416).take 8 = (ports416.drop 0).take 8

numeric_data_binding portsPiece416 : (ports416.drop 0).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program.drop 416).take 8).map encodePort

theorem portsSlice416 : (ports.drop 416).take 8 = (sourcePorts.drop 416).take 8 :=
  portsView416.trans (portsPiece416.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program encodePort 416 8))

numeric_data_binding portsView424 : (ports.drop 424).take 8 = (ports416.drop 8).take 8

numeric_data_binding portsPiece424 : (ports416.drop 8).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program.drop 424).take 8).map encodePort

theorem portsSlice424 : (ports.drop 424).take 8 = (sourcePorts.drop 424).take 8 :=
  portsView424.trans (portsPiece424.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program encodePort 424 8))

numeric_data_binding portsView432 : (ports.drop 432).take 8 = (ports416.drop 16).take 8

numeric_data_binding portsPiece432 : (ports416.drop 16).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program.drop 432).take 8).map encodePort

theorem portsSlice432 : (ports.drop 432).take 8 = (sourcePorts.drop 432).take 8 :=
  portsView432.trans (portsPiece432.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program encodePort 432 8))

numeric_data_binding portsView440 : (ports.drop 440).take 8 = (ports416.drop 24).take 8

numeric_data_binding portsPiece440 : (ports416.drop 24).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program.drop 440).take 8).map encodePort

theorem portsSlice440 : (ports.drop 440).take 8 = (sourcePorts.drop 440).take 8 :=
  portsView440.trans (portsPiece440.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program encodePort 440 8))

numeric_data_binding portsView448 : (ports.drop 448).take 8 = (ports448.drop 0).take 8

numeric_data_binding portsPiece448 : (ports448.drop 0).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program.drop 448).take 8).map encodePort

theorem portsSlice448 : (ports.drop 448).take 8 = (sourcePorts.drop 448).take 8 :=
  portsView448.trans (portsPiece448.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program encodePort 448 8))

numeric_data_binding portsView456 : (ports.drop 456).take 8 = (ports448.drop 8).take 8

numeric_data_binding portsPiece456 : (ports448.drop 8).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program.drop 456).take 8).map encodePort

theorem portsSlice456 : (ports.drop 456).take 8 = (sourcePorts.drop 456).take 8 :=
  portsView456.trans (portsPiece456.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program encodePort 456 8))

numeric_data_binding portsView464 : (ports.drop 464).take 8 = (ports448.drop 16).take 8

numeric_data_binding portsPiece464 : (ports448.drop 16).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program.drop 464).take 8).map encodePort

theorem portsSlice464 : (ports.drop 464).take 8 = (sourcePorts.drop 464).take 8 :=
  portsView464.trans (portsPiece464.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program encodePort 464 8))

numeric_data_binding portsView472 : (ports.drop 472).take 8 = (ports448.drop 24).take 8

numeric_data_binding portsPiece472 : (ports448.drop 24).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program.drop 472).take 8).map encodePort

theorem portsSlice472 : (ports.drop 472).take 8 = (sourcePorts.drop 472).take 8 :=
  portsView472.trans (portsPiece472.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program encodePort 472 8))

numeric_data_binding portsView480 : (ports.drop 480).take 8 = (ports480.drop 0).take 8

numeric_data_binding portsPiece480 : (ports480.drop 0).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program.drop 480).take 8).map encodePort

theorem portsSlice480 : (ports.drop 480).take 8 = (sourcePorts.drop 480).take 8 :=
  portsView480.trans (portsPiece480.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program encodePort 480 8))

numeric_data_binding portsView488 : (ports.drop 488).take 8 = (ports480.drop 8).take 8

numeric_data_binding portsPiece488 : (ports480.drop 8).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program.drop 488).take 8).map encodePort

theorem portsSlice488 : (ports.drop 488).take 8 = (sourcePorts.drop 488).take 8 :=
  portsView488.trans (portsPiece488.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program encodePort 488 8))

numeric_data_binding portsView496 : (ports.drop 496).take 8 = (ports480.drop 16).take 8

numeric_data_binding portsPiece496 : (ports480.drop 16).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program.drop 496).take 8).map encodePort

theorem portsSlice496 : (ports.drop 496).take 8 = (sourcePorts.drop 496).take 8 :=
  portsView496.trans (portsPiece496.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program encodePort 496 8))

numeric_data_binding portsView504 : (ports.drop 504).take 8 = (ports480.drop 24).take 8

numeric_data_binding portsPiece504 : (ports480.drop 24).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program.drop 504).take 8).map encodePort

theorem portsSlice504 : (ports.drop 504).take 8 = (sourcePorts.drop 504).take 8 :=
  portsView504.trans (portsPiece504.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program encodePort 504 8))

numeric_data_binding portsView512 : (ports.drop 512).take 8 = (ports512.drop 0).take 8

numeric_data_binding portsPiece512 : (ports512.drop 0).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program.drop 512).take 8).map encodePort

theorem portsSlice512 : (ports.drop 512).take 8 = (sourcePorts.drop 512).take 8 :=
  portsView512.trans (portsPiece512.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program encodePort 512 8))

numeric_data_binding portsView520 : (ports.drop 520).take 8 = (ports512.drop 8).take 8

numeric_data_binding portsPiece520 : (ports512.drop 8).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program.drop 520).take 8).map encodePort

theorem portsSlice520 : (ports.drop 520).take 8 = (sourcePorts.drop 520).take 8 :=
  portsView520.trans (portsPiece520.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program encodePort 520 8))

numeric_data_binding portsView528 : (ports.drop 528).take 8 = (ports512.drop 16).take 8

numeric_data_binding portsPiece528 : (ports512.drop 16).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program.drop 528).take 8).map encodePort

theorem portsSlice528 : (ports.drop 528).take 8 = (sourcePorts.drop 528).take 8 :=
  portsView528.trans (portsPiece528.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program encodePort 528 8))

numeric_data_binding portsView536 : (ports.drop 536).take 8 = (ports512.drop 24).take 8

numeric_data_binding portsPiece536 : (ports512.drop 24).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program.drop 536).take 8).map encodePort

theorem portsSlice536 : (ports.drop 536).take 8 = (sourcePorts.drop 536).take 8 :=
  portsView536.trans (portsPiece536.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program encodePort 536 8))

numeric_data_binding portsView544 : (ports.drop 544).take 8 = (ports544.drop 0).take 8

numeric_data_binding portsPiece544 : (ports544.drop 0).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program.drop 544).take 8).map encodePort

theorem portsSlice544 : (ports.drop 544).take 8 = (sourcePorts.drop 544).take 8 :=
  portsView544.trans (portsPiece544.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program encodePort 544 8))

numeric_data_binding portsView552 : (ports.drop 552).take 8 = (ports544.drop 8).take 8

numeric_data_binding portsPiece552 : (ports544.drop 8).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program.drop 552).take 8).map encodePort

theorem portsSlice552 : (ports.drop 552).take 8 = (sourcePorts.drop 552).take 8 :=
  portsView552.trans (portsPiece552.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program encodePort 552 8))

numeric_data_binding portsView560 : (ports.drop 560).take 8 = (ports544.drop 16).take 8

numeric_data_binding portsPiece560 : (ports544.drop 16).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program.drop 560).take 8).map encodePort

theorem portsSlice560 : (ports.drop 560).take 8 = (sourcePorts.drop 560).take 8 :=
  portsView560.trans (portsPiece560.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program encodePort 560 8))

numeric_data_binding portsView568 : (ports.drop 568).take 8 = (ports544.drop 24).take 8

numeric_data_binding portsPiece568 : (ports544.drop 24).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program.drop 568).take 8).map encodePort

theorem portsSlice568 : (ports.drop 568).take 8 = (sourcePorts.drop 568).take 8 :=
  portsView568.trans (portsPiece568.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program encodePort 568 8))

numeric_data_binding portsView576 : (ports.drop 576).take 8 = (ports576.drop 0).take 8

numeric_data_binding portsPiece576 : (ports576.drop 0).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program.drop 576).take 8).map encodePort

theorem portsSlice576 : (ports.drop 576).take 8 = (sourcePorts.drop 576).take 8 :=
  portsView576.trans (portsPiece576.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program encodePort 576 8))

numeric_data_binding portsView584 : (ports.drop 584).take 8 = (ports576.drop 8).take 8

numeric_data_binding portsPiece584 : (ports576.drop 8).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program.drop 584).take 8).map encodePort

theorem portsSlice584 : (ports.drop 584).take 8 = (sourcePorts.drop 584).take 8 :=
  portsView584.trans (portsPiece584.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program encodePort 584 8))

numeric_data_binding portsView592 : (ports.drop 592).take 8 = (ports576.drop 16).take 8

numeric_data_binding portsPiece592 : (ports576.drop 16).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program.drop 592).take 8).map encodePort

theorem portsSlice592 : (ports.drop 592).take 8 = (sourcePorts.drop 592).take 8 :=
  portsView592.trans (portsPiece592.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program encodePort 592 8))

numeric_data_binding portsView600 : (ports.drop 600).take 8 = (ports576.drop 24).take 8

numeric_data_binding portsPiece600 : (ports576.drop 24).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program.drop 600).take 8).map encodePort

theorem portsSlice600 : (ports.drop 600).take 8 = (sourcePorts.drop 600).take 8 :=
  portsView600.trans (portsPiece600.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program encodePort 600 8))

numeric_data_binding portsView608 : (ports.drop 608).take 8 = (ports608.drop 0).take 8

numeric_data_binding portsPiece608 : (ports608.drop 0).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program.drop 608).take 8).map encodePort

theorem portsSlice608 : (ports.drop 608).take 8 = (sourcePorts.drop 608).take 8 :=
  portsView608.trans (portsPiece608.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program encodePort 608 8))

numeric_data_binding portsView616 : (ports.drop 616).take 8 = (ports608.drop 8).take 8

numeric_data_binding portsPiece616 : (ports608.drop 8).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program.drop 616).take 8).map encodePort

theorem portsSlice616 : (ports.drop 616).take 8 = (sourcePorts.drop 616).take 8 :=
  portsView616.trans (portsPiece616.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program encodePort 616 8))

numeric_data_binding portsView624 : (ports.drop 624).take 8 = (ports608.drop 16).take 8

numeric_data_binding portsPiece624 : (ports608.drop 16).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program.drop 624).take 8).map encodePort

theorem portsSlice624 : (ports.drop 624).take 8 = (sourcePorts.drop 624).take 8 :=
  portsView624.trans (portsPiece624.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program encodePort 624 8))

numeric_data_binding portsView632 : (ports.drop 632).take 8 = (ports608.drop 24).take 8

numeric_data_binding portsPiece632 : (ports608.drop 24).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program.drop 632).take 8).map encodePort

theorem portsSlice632 : (ports.drop 632).take 8 = (sourcePorts.drop 632).take 8 :=
  portsView632.trans (portsPiece632.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program encodePort 632 8))

numeric_data_binding portsView640 : (ports.drop 640).take 8 = (ports640.drop 0).take 8

numeric_data_binding portsPiece640 : (ports640.drop 0).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program.drop 640).take 8).map encodePort

theorem portsSlice640 : (ports.drop 640).take 8 = (sourcePorts.drop 640).take 8 :=
  portsView640.trans (portsPiece640.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program encodePort 640 8))

numeric_data_binding portsView648 : (ports.drop 648).take 8 = (ports640.drop 8).take 8

numeric_data_binding portsPiece648 : (ports640.drop 8).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program.drop 648).take 8).map encodePort

theorem portsSlice648 : (ports.drop 648).take 8 = (sourcePorts.drop 648).take 8 :=
  portsView648.trans (portsPiece648.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program encodePort 648 8))

numeric_data_binding portsView656 : (ports.drop 656).take 8 = (ports640.drop 16).take 8

numeric_data_binding portsPiece656 : (ports640.drop 16).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program.drop 656).take 8).map encodePort

theorem portsSlice656 : (ports.drop 656).take 8 = (sourcePorts.drop 656).take 8 :=
  portsView656.trans (portsPiece656.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program encodePort 656 8))

numeric_data_binding portsView664 : (ports.drop 664).take 8 = (ports640.drop 24).take 8

numeric_data_binding portsPiece664 : (ports640.drop 24).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program.drop 664).take 8).map encodePort

theorem portsSlice664 : (ports.drop 664).take 8 = (sourcePorts.drop 664).take 8 :=
  portsView664.trans (portsPiece664.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program encodePort 664 8))

numeric_data_binding portsView672 : (ports.drop 672).take 2 = (ports672.drop 0).take 2

numeric_data_binding portsPiece672 : (ports672.drop 0).take 2 = ((Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program.drop 672).take 2).map encodePort

theorem portsSlice672 : (ports.drop 672).take 2 = (sourcePorts.drop 672).take 2 :=
  portsView672.trans (portsPiece672.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program encodePort 672 2))

theorem portsNode0_16 : (ports.drop 0).take 16 = (sourcePorts.drop 0).take 16 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 0 8 8 portsSlice0 portsSlice8

theorem portsNode24_16 : (ports.drop 24).take 16 = (sourcePorts.drop 24).take 16 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 24 8 8 portsSlice24 portsSlice32

theorem portsNode16_24 : (ports.drop 16).take 24 = (sourcePorts.drop 16).take 24 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 16 8 16 portsSlice16 portsNode24_16

theorem portsNode0_40 : (ports.drop 0).take 40 = (sourcePorts.drop 0).take 40 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 0 16 24 portsNode0_16 portsNode16_24

theorem portsNode40_16 : (ports.drop 40).take 16 = (sourcePorts.drop 40).take 16 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 40 8 8 portsSlice40 portsSlice48

theorem portsNode64_16 : (ports.drop 64).take 16 = (sourcePorts.drop 64).take 16 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 64 8 8 portsSlice64 portsSlice72

theorem portsNode56_24 : (ports.drop 56).take 24 = (sourcePorts.drop 56).take 24 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 56 8 16 portsSlice56 portsNode64_16

theorem portsNode40_40 : (ports.drop 40).take 40 = (sourcePorts.drop 40).take 40 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 40 16 24 portsNode40_16 portsNode56_24

theorem portsNode0_80 : (ports.drop 0).take 80 = (sourcePorts.drop 0).take 80 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 0 40 40 portsNode0_40 portsNode40_40

theorem portsNode80_16 : (ports.drop 80).take 16 = (sourcePorts.drop 80).take 16 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 80 8 8 portsSlice80 portsSlice88

theorem portsNode104_16 : (ports.drop 104).take 16 = (sourcePorts.drop 104).take 16 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 104 8 8 portsSlice104 portsSlice112

theorem portsNode96_24 : (ports.drop 96).take 24 = (sourcePorts.drop 96).take 24 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 96 8 16 portsSlice96 portsNode104_16

theorem portsNode80_40 : (ports.drop 80).take 40 = (sourcePorts.drop 80).take 40 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 80 16 24 portsNode80_16 portsNode96_24

theorem portsNode128_16 : (ports.drop 128).take 16 = (sourcePorts.drop 128).take 16 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 128 8 8 portsSlice128 portsSlice136

theorem portsNode120_24 : (ports.drop 120).take 24 = (sourcePorts.drop 120).take 24 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 120 8 16 portsSlice120 portsNode128_16

theorem portsNode152_16 : (ports.drop 152).take 16 = (sourcePorts.drop 152).take 16 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 152 8 8 portsSlice152 portsSlice160

theorem portsNode144_24 : (ports.drop 144).take 24 = (sourcePorts.drop 144).take 24 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 144 8 16 portsSlice144 portsNode152_16

theorem portsNode120_48 : (ports.drop 120).take 48 = (sourcePorts.drop 120).take 48 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 120 24 24 portsNode120_24 portsNode144_24

theorem portsNode80_88 : (ports.drop 80).take 88 = (sourcePorts.drop 80).take 88 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 80 40 48 portsNode80_40 portsNode120_48

theorem portsNode0_168 : (ports.drop 0).take 168 = (sourcePorts.drop 0).take 168 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 0 80 88 portsNode0_80 portsNode80_88

theorem portsNode168_16 : (ports.drop 168).take 16 = (sourcePorts.drop 168).take 16 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 168 8 8 portsSlice168 portsSlice176

theorem portsNode192_16 : (ports.drop 192).take 16 = (sourcePorts.drop 192).take 16 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 192 8 8 portsSlice192 portsSlice200

theorem portsNode184_24 : (ports.drop 184).take 24 = (sourcePorts.drop 184).take 24 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 184 8 16 portsSlice184 portsNode192_16

theorem portsNode168_40 : (ports.drop 168).take 40 = (sourcePorts.drop 168).take 40 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 168 16 24 portsNode168_16 portsNode184_24

theorem portsNode208_16 : (ports.drop 208).take 16 = (sourcePorts.drop 208).take 16 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 208 8 8 portsSlice208 portsSlice216

theorem portsNode232_16 : (ports.drop 232).take 16 = (sourcePorts.drop 232).take 16 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 232 8 8 portsSlice232 portsSlice240

theorem portsNode224_24 : (ports.drop 224).take 24 = (sourcePorts.drop 224).take 24 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 224 8 16 portsSlice224 portsNode232_16

theorem portsNode208_40 : (ports.drop 208).take 40 = (sourcePorts.drop 208).take 40 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 208 16 24 portsNode208_16 portsNode224_24

theorem portsNode168_80 : (ports.drop 168).take 80 = (sourcePorts.drop 168).take 80 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 168 40 40 portsNode168_40 portsNode208_40

theorem portsNode248_16 : (ports.drop 248).take 16 = (sourcePorts.drop 248).take 16 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 248 8 8 portsSlice248 portsSlice256

theorem portsNode272_16 : (ports.drop 272).take 16 = (sourcePorts.drop 272).take 16 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 272 8 8 portsSlice272 portsSlice280

theorem portsNode264_24 : (ports.drop 264).take 24 = (sourcePorts.drop 264).take 24 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 264 8 16 portsSlice264 portsNode272_16

theorem portsNode248_40 : (ports.drop 248).take 40 = (sourcePorts.drop 248).take 40 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 248 16 24 portsNode248_16 portsNode264_24

theorem portsNode296_16 : (ports.drop 296).take 16 = (sourcePorts.drop 296).take 16 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 296 8 8 portsSlice296 portsSlice304

theorem portsNode288_24 : (ports.drop 288).take 24 = (sourcePorts.drop 288).take 24 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 288 8 16 portsSlice288 portsNode296_16

theorem portsNode320_16 : (ports.drop 320).take 16 = (sourcePorts.drop 320).take 16 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 320 8 8 portsSlice320 portsSlice328

theorem portsNode312_24 : (ports.drop 312).take 24 = (sourcePorts.drop 312).take 24 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 312 8 16 portsSlice312 portsNode320_16

theorem portsNode288_48 : (ports.drop 288).take 48 = (sourcePorts.drop 288).take 48 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 288 24 24 portsNode288_24 portsNode312_24

theorem portsNode248_88 : (ports.drop 248).take 88 = (sourcePorts.drop 248).take 88 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 248 40 48 portsNode248_40 portsNode288_48

theorem portsNode168_168 : (ports.drop 168).take 168 = (sourcePorts.drop 168).take 168 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 168 80 88 portsNode168_80 portsNode248_88

theorem portsNode0_336 : (ports.drop 0).take 336 = (sourcePorts.drop 0).take 336 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 0 168 168 portsNode0_168 portsNode168_168

theorem portsNode336_16 : (ports.drop 336).take 16 = (sourcePorts.drop 336).take 16 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 336 8 8 portsSlice336 portsSlice344

theorem portsNode360_16 : (ports.drop 360).take 16 = (sourcePorts.drop 360).take 16 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 360 8 8 portsSlice360 portsSlice368

theorem portsNode352_24 : (ports.drop 352).take 24 = (sourcePorts.drop 352).take 24 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 352 8 16 portsSlice352 portsNode360_16

theorem portsNode336_40 : (ports.drop 336).take 40 = (sourcePorts.drop 336).take 40 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 336 16 24 portsNode336_16 portsNode352_24

theorem portsNode376_16 : (ports.drop 376).take 16 = (sourcePorts.drop 376).take 16 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 376 8 8 portsSlice376 portsSlice384

theorem portsNode400_16 : (ports.drop 400).take 16 = (sourcePorts.drop 400).take 16 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 400 8 8 portsSlice400 portsSlice408

theorem portsNode392_24 : (ports.drop 392).take 24 = (sourcePorts.drop 392).take 24 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 392 8 16 portsSlice392 portsNode400_16

theorem portsNode376_40 : (ports.drop 376).take 40 = (sourcePorts.drop 376).take 40 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 376 16 24 portsNode376_16 portsNode392_24

theorem portsNode336_80 : (ports.drop 336).take 80 = (sourcePorts.drop 336).take 80 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 336 40 40 portsNode336_40 portsNode376_40

theorem portsNode416_16 : (ports.drop 416).take 16 = (sourcePorts.drop 416).take 16 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 416 8 8 portsSlice416 portsSlice424

theorem portsNode440_16 : (ports.drop 440).take 16 = (sourcePorts.drop 440).take 16 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 440 8 8 portsSlice440 portsSlice448

theorem portsNode432_24 : (ports.drop 432).take 24 = (sourcePorts.drop 432).take 24 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 432 8 16 portsSlice432 portsNode440_16

theorem portsNode416_40 : (ports.drop 416).take 40 = (sourcePorts.drop 416).take 40 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 416 16 24 portsNode416_16 portsNode432_24

theorem portsNode464_16 : (ports.drop 464).take 16 = (sourcePorts.drop 464).take 16 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 464 8 8 portsSlice464 portsSlice472

theorem portsNode456_24 : (ports.drop 456).take 24 = (sourcePorts.drop 456).take 24 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 456 8 16 portsSlice456 portsNode464_16

theorem portsNode488_16 : (ports.drop 488).take 16 = (sourcePorts.drop 488).take 16 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 488 8 8 portsSlice488 portsSlice496

theorem portsNode480_24 : (ports.drop 480).take 24 = (sourcePorts.drop 480).take 24 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 480 8 16 portsSlice480 portsNode488_16

theorem portsNode456_48 : (ports.drop 456).take 48 = (sourcePorts.drop 456).take 48 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 456 24 24 portsNode456_24 portsNode480_24

theorem portsNode416_88 : (ports.drop 416).take 88 = (sourcePorts.drop 416).take 88 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 416 40 48 portsNode416_40 portsNode456_48

theorem portsNode336_168 : (ports.drop 336).take 168 = (sourcePorts.drop 336).take 168 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 336 80 88 portsNode336_80 portsNode416_88

theorem portsNode504_16 : (ports.drop 504).take 16 = (sourcePorts.drop 504).take 16 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 504 8 8 portsSlice504 portsSlice512

theorem portsNode528_16 : (ports.drop 528).take 16 = (sourcePorts.drop 528).take 16 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 528 8 8 portsSlice528 portsSlice536

theorem portsNode520_24 : (ports.drop 520).take 24 = (sourcePorts.drop 520).take 24 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 520 8 16 portsSlice520 portsNode528_16

theorem portsNode504_40 : (ports.drop 504).take 40 = (sourcePorts.drop 504).take 40 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 504 16 24 portsNode504_16 portsNode520_24

theorem portsNode552_16 : (ports.drop 552).take 16 = (sourcePorts.drop 552).take 16 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 552 8 8 portsSlice552 portsSlice560

theorem portsNode544_24 : (ports.drop 544).take 24 = (sourcePorts.drop 544).take 24 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 544 8 16 portsSlice544 portsNode552_16

theorem portsNode576_16 : (ports.drop 576).take 16 = (sourcePorts.drop 576).take 16 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 576 8 8 portsSlice576 portsSlice584

theorem portsNode568_24 : (ports.drop 568).take 24 = (sourcePorts.drop 568).take 24 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 568 8 16 portsSlice568 portsNode576_16

theorem portsNode544_48 : (ports.drop 544).take 48 = (sourcePorts.drop 544).take 48 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 544 24 24 portsNode544_24 portsNode568_24

theorem portsNode504_88 : (ports.drop 504).take 88 = (sourcePorts.drop 504).take 88 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 504 40 48 portsNode504_40 portsNode544_48

theorem portsNode592_16 : (ports.drop 592).take 16 = (sourcePorts.drop 592).take 16 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 592 8 8 portsSlice592 portsSlice600

theorem portsNode616_16 : (ports.drop 616).take 16 = (sourcePorts.drop 616).take 16 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 616 8 8 portsSlice616 portsSlice624

theorem portsNode608_24 : (ports.drop 608).take 24 = (sourcePorts.drop 608).take 24 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 608 8 16 portsSlice608 portsNode616_16

theorem portsNode592_40 : (ports.drop 592).take 40 = (sourcePorts.drop 592).take 40 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 592 16 24 portsNode592_16 portsNode608_24

theorem portsNode640_16 : (ports.drop 640).take 16 = (sourcePorts.drop 640).take 16 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 640 8 8 portsSlice640 portsSlice648

theorem portsNode632_24 : (ports.drop 632).take 24 = (sourcePorts.drop 632).take 24 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 632 8 16 portsSlice632 portsNode640_16

theorem portsNode664_10 : (ports.drop 664).take 10 = (sourcePorts.drop 664).take 10 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 664 8 2 portsSlice664 portsSlice672

theorem portsNode656_18 : (ports.drop 656).take 18 = (sourcePorts.drop 656).take 18 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 656 8 10 portsSlice656 portsNode664_10

theorem portsNode632_42 : (ports.drop 632).take 42 = (sourcePorts.drop 632).take 42 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 632 24 18 portsNode632_24 portsNode656_18

theorem portsNode592_82 : (ports.drop 592).take 82 = (sourcePorts.drop 592).take 82 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 592 40 42 portsNode592_40 portsNode632_42

theorem portsNode504_170 : (ports.drop 504).take 170 = (sourcePorts.drop 504).take 170 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 504 88 82 portsNode504_88 portsNode592_82

theorem portsNode336_338 : (ports.drop 336).take 338 = (sourcePorts.drop 336).take 338 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 336 168 170 portsNode336_168 portsNode504_170

theorem portsNode0_674 : (ports.drop 0).take 674 = (sourcePorts.drop 0).take 674 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 0 336 338 portsNode0_336 portsNode336_338

theorem programLength : Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.program.length = 674 := by decide +kernel

theorem ports_binding : ports = sourcePorts :=
  NumericQueryFrameChecks.complete_binding ports sourcePorts 674
    (by decide +kernel) (by rw [sourcePorts, List.length_map, programLength]) portsNode0_674

end Airbender.Compiler.FunctionalStepChecks.BlakeRoundCached
