import Airbender.Proofs.GKRProtocol.FunctionalStepChecks.BlakeRoundUncached.Data
import Airbender.Proofs.GKRProtocol.FunctionalNative.BlakeRoundUncachedFoundation
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.FunctionalStepChecks.BlakeRoundUncached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def encodePort (step : FunctionalStep) := NumericFunctionalStepChecks.encode Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.isBase ([], step)

noncomputable def sourcePorts := Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.program.map encodePort

numeric_data_binding portsView0 : (ports.drop 0).take 8 = (ports0.drop 0).take 8

numeric_data_binding portsPiece0 : (ports0.drop 0).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.program.drop 0).take 8).map encodePort

theorem portsSlice0 : (ports.drop 0).take 8 = (sourcePorts.drop 0).take 8 :=
  portsView0.trans (portsPiece0.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.program encodePort 0 8))

numeric_data_binding portsView8 : (ports.drop 8).take 8 = (ports0.drop 8).take 8

numeric_data_binding portsPiece8 : (ports0.drop 8).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.program.drop 8).take 8).map encodePort

theorem portsSlice8 : (ports.drop 8).take 8 = (sourcePorts.drop 8).take 8 :=
  portsView8.trans (portsPiece8.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.program encodePort 8 8))

numeric_data_binding portsView16 : (ports.drop 16).take 8 = (ports0.drop 16).take 8

numeric_data_binding portsPiece16 : (ports0.drop 16).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.program.drop 16).take 8).map encodePort

theorem portsSlice16 : (ports.drop 16).take 8 = (sourcePorts.drop 16).take 8 :=
  portsView16.trans (portsPiece16.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.program encodePort 16 8))

numeric_data_binding portsView24 : (ports.drop 24).take 8 = (ports0.drop 24).take 8

numeric_data_binding portsPiece24 : (ports0.drop 24).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.program.drop 24).take 8).map encodePort

theorem portsSlice24 : (ports.drop 24).take 8 = (sourcePorts.drop 24).take 8 :=
  portsView24.trans (portsPiece24.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.program encodePort 24 8))

numeric_data_binding portsView32 : (ports.drop 32).take 8 = (ports32.drop 0).take 8

numeric_data_binding portsPiece32 : (ports32.drop 0).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.program.drop 32).take 8).map encodePort

theorem portsSlice32 : (ports.drop 32).take 8 = (sourcePorts.drop 32).take 8 :=
  portsView32.trans (portsPiece32.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.program encodePort 32 8))

numeric_data_binding portsView40 : (ports.drop 40).take 8 = (ports32.drop 8).take 8

numeric_data_binding portsPiece40 : (ports32.drop 8).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.program.drop 40).take 8).map encodePort

theorem portsSlice40 : (ports.drop 40).take 8 = (sourcePorts.drop 40).take 8 :=
  portsView40.trans (portsPiece40.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.program encodePort 40 8))

numeric_data_binding portsView48 : (ports.drop 48).take 8 = (ports32.drop 16).take 8

numeric_data_binding portsPiece48 : (ports32.drop 16).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.program.drop 48).take 8).map encodePort

theorem portsSlice48 : (ports.drop 48).take 8 = (sourcePorts.drop 48).take 8 :=
  portsView48.trans (portsPiece48.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.program encodePort 48 8))

numeric_data_binding portsView56 : (ports.drop 56).take 8 = (ports32.drop 24).take 8

numeric_data_binding portsPiece56 : (ports32.drop 24).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.program.drop 56).take 8).map encodePort

theorem portsSlice56 : (ports.drop 56).take 8 = (sourcePorts.drop 56).take 8 :=
  portsView56.trans (portsPiece56.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.program encodePort 56 8))

numeric_data_binding portsView64 : (ports.drop 64).take 8 = (ports64.drop 0).take 8

numeric_data_binding portsPiece64 : (ports64.drop 0).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.program.drop 64).take 8).map encodePort

theorem portsSlice64 : (ports.drop 64).take 8 = (sourcePorts.drop 64).take 8 :=
  portsView64.trans (portsPiece64.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.program encodePort 64 8))

numeric_data_binding portsView72 : (ports.drop 72).take 8 = (ports64.drop 8).take 8

numeric_data_binding portsPiece72 : (ports64.drop 8).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.program.drop 72).take 8).map encodePort

theorem portsSlice72 : (ports.drop 72).take 8 = (sourcePorts.drop 72).take 8 :=
  portsView72.trans (portsPiece72.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.program encodePort 72 8))

numeric_data_binding portsView80 : (ports.drop 80).take 8 = (ports64.drop 16).take 8

numeric_data_binding portsPiece80 : (ports64.drop 16).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.program.drop 80).take 8).map encodePort

theorem portsSlice80 : (ports.drop 80).take 8 = (sourcePorts.drop 80).take 8 :=
  portsView80.trans (portsPiece80.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.program encodePort 80 8))

numeric_data_binding portsView88 : (ports.drop 88).take 8 = (ports64.drop 24).take 8

numeric_data_binding portsPiece88 : (ports64.drop 24).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.program.drop 88).take 8).map encodePort

theorem portsSlice88 : (ports.drop 88).take 8 = (sourcePorts.drop 88).take 8 :=
  portsView88.trans (portsPiece88.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.program encodePort 88 8))

numeric_data_binding portsView96 : (ports.drop 96).take 8 = (ports96.drop 0).take 8

numeric_data_binding portsPiece96 : (ports96.drop 0).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.program.drop 96).take 8).map encodePort

theorem portsSlice96 : (ports.drop 96).take 8 = (sourcePorts.drop 96).take 8 :=
  portsView96.trans (portsPiece96.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.program encodePort 96 8))

numeric_data_binding portsView104 : (ports.drop 104).take 8 = (ports96.drop 8).take 8

numeric_data_binding portsPiece104 : (ports96.drop 8).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.program.drop 104).take 8).map encodePort

theorem portsSlice104 : (ports.drop 104).take 8 = (sourcePorts.drop 104).take 8 :=
  portsView104.trans (portsPiece104.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.program encodePort 104 8))

numeric_data_binding portsView112 : (ports.drop 112).take 8 = (ports96.drop 16).take 8

numeric_data_binding portsPiece112 : (ports96.drop 16).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.program.drop 112).take 8).map encodePort

theorem portsSlice112 : (ports.drop 112).take 8 = (sourcePorts.drop 112).take 8 :=
  portsView112.trans (portsPiece112.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.program encodePort 112 8))

numeric_data_binding portsView120 : (ports.drop 120).take 8 = (ports96.drop 24).take 8

numeric_data_binding portsPiece120 : (ports96.drop 24).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.program.drop 120).take 8).map encodePort

theorem portsSlice120 : (ports.drop 120).take 8 = (sourcePorts.drop 120).take 8 :=
  portsView120.trans (portsPiece120.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.program encodePort 120 8))

numeric_data_binding portsView128 : (ports.drop 128).take 8 = (ports128.drop 0).take 8

numeric_data_binding portsPiece128 : (ports128.drop 0).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.program.drop 128).take 8).map encodePort

theorem portsSlice128 : (ports.drop 128).take 8 = (sourcePorts.drop 128).take 8 :=
  portsView128.trans (portsPiece128.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.program encodePort 128 8))

numeric_data_binding portsView136 : (ports.drop 136).take 8 = (ports128.drop 8).take 8

numeric_data_binding portsPiece136 : (ports128.drop 8).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.program.drop 136).take 8).map encodePort

theorem portsSlice136 : (ports.drop 136).take 8 = (sourcePorts.drop 136).take 8 :=
  portsView136.trans (portsPiece136.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.program encodePort 136 8))

numeric_data_binding portsView144 : (ports.drop 144).take 8 = (ports128.drop 16).take 8

numeric_data_binding portsPiece144 : (ports128.drop 16).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.program.drop 144).take 8).map encodePort

theorem portsSlice144 : (ports.drop 144).take 8 = (sourcePorts.drop 144).take 8 :=
  portsView144.trans (portsPiece144.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.program encodePort 144 8))

numeric_data_binding portsView152 : (ports.drop 152).take 8 = (ports128.drop 24).take 8

numeric_data_binding portsPiece152 : (ports128.drop 24).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.program.drop 152).take 8).map encodePort

theorem portsSlice152 : (ports.drop 152).take 8 = (sourcePorts.drop 152).take 8 :=
  portsView152.trans (portsPiece152.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.program encodePort 152 8))

numeric_data_binding portsView160 : (ports.drop 160).take 8 = (ports160.drop 0).take 8

numeric_data_binding portsPiece160 : (ports160.drop 0).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.program.drop 160).take 8).map encodePort

theorem portsSlice160 : (ports.drop 160).take 8 = (sourcePorts.drop 160).take 8 :=
  portsView160.trans (portsPiece160.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.program encodePort 160 8))

numeric_data_binding portsView168 : (ports.drop 168).take 8 = (ports160.drop 8).take 8

numeric_data_binding portsPiece168 : (ports160.drop 8).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.program.drop 168).take 8).map encodePort

theorem portsSlice168 : (ports.drop 168).take 8 = (sourcePorts.drop 168).take 8 :=
  portsView168.trans (portsPiece168.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.program encodePort 168 8))

numeric_data_binding portsView176 : (ports.drop 176).take 8 = (ports160.drop 16).take 8

numeric_data_binding portsPiece176 : (ports160.drop 16).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.program.drop 176).take 8).map encodePort

theorem portsSlice176 : (ports.drop 176).take 8 = (sourcePorts.drop 176).take 8 :=
  portsView176.trans (portsPiece176.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.program encodePort 176 8))

numeric_data_binding portsView184 : (ports.drop 184).take 8 = (ports160.drop 24).take 8

numeric_data_binding portsPiece184 : (ports160.drop 24).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.program.drop 184).take 8).map encodePort

theorem portsSlice184 : (ports.drop 184).take 8 = (sourcePorts.drop 184).take 8 :=
  portsView184.trans (portsPiece184.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.program encodePort 184 8))

numeric_data_binding portsView192 : (ports.drop 192).take 8 = (ports192.drop 0).take 8

numeric_data_binding portsPiece192 : (ports192.drop 0).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.program.drop 192).take 8).map encodePort

theorem portsSlice192 : (ports.drop 192).take 8 = (sourcePorts.drop 192).take 8 :=
  portsView192.trans (portsPiece192.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.program encodePort 192 8))

numeric_data_binding portsView200 : (ports.drop 200).take 8 = (ports192.drop 8).take 8

numeric_data_binding portsPiece200 : (ports192.drop 8).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.program.drop 200).take 8).map encodePort

theorem portsSlice200 : (ports.drop 200).take 8 = (sourcePorts.drop 200).take 8 :=
  portsView200.trans (portsPiece200.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.program encodePort 200 8))

numeric_data_binding portsView208 : (ports.drop 208).take 8 = (ports192.drop 16).take 8

numeric_data_binding portsPiece208 : (ports192.drop 16).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.program.drop 208).take 8).map encodePort

theorem portsSlice208 : (ports.drop 208).take 8 = (sourcePorts.drop 208).take 8 :=
  portsView208.trans (portsPiece208.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.program encodePort 208 8))

numeric_data_binding portsView216 : (ports.drop 216).take 8 = (ports192.drop 24).take 8

numeric_data_binding portsPiece216 : (ports192.drop 24).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.program.drop 216).take 8).map encodePort

theorem portsSlice216 : (ports.drop 216).take 8 = (sourcePorts.drop 216).take 8 :=
  portsView216.trans (portsPiece216.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.program encodePort 216 8))

numeric_data_binding portsView224 : (ports.drop 224).take 8 = (ports224.drop 0).take 8

numeric_data_binding portsPiece224 : (ports224.drop 0).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.program.drop 224).take 8).map encodePort

theorem portsSlice224 : (ports.drop 224).take 8 = (sourcePorts.drop 224).take 8 :=
  portsView224.trans (portsPiece224.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.program encodePort 224 8))

numeric_data_binding portsView232 : (ports.drop 232).take 8 = (ports224.drop 8).take 8

numeric_data_binding portsPiece232 : (ports224.drop 8).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.program.drop 232).take 8).map encodePort

theorem portsSlice232 : (ports.drop 232).take 8 = (sourcePorts.drop 232).take 8 :=
  portsView232.trans (portsPiece232.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.program encodePort 232 8))

numeric_data_binding portsView240 : (ports.drop 240).take 8 = (ports224.drop 16).take 8

numeric_data_binding portsPiece240 : (ports224.drop 16).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.program.drop 240).take 8).map encodePort

theorem portsSlice240 : (ports.drop 240).take 8 = (sourcePorts.drop 240).take 8 :=
  portsView240.trans (portsPiece240.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.program encodePort 240 8))

numeric_data_binding portsView248 : (ports.drop 248).take 8 = (ports224.drop 24).take 8

numeric_data_binding portsPiece248 : (ports224.drop 24).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.program.drop 248).take 8).map encodePort

theorem portsSlice248 : (ports.drop 248).take 8 = (sourcePorts.drop 248).take 8 :=
  portsView248.trans (portsPiece248.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.program encodePort 248 8))

numeric_data_binding portsView256 : (ports.drop 256).take 8 = (ports256.drop 0).take 8

numeric_data_binding portsPiece256 : (ports256.drop 0).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.program.drop 256).take 8).map encodePort

theorem portsSlice256 : (ports.drop 256).take 8 = (sourcePorts.drop 256).take 8 :=
  portsView256.trans (portsPiece256.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.program encodePort 256 8))

numeric_data_binding portsView264 : (ports.drop 264).take 8 = (ports256.drop 8).take 8

numeric_data_binding portsPiece264 : (ports256.drop 8).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.program.drop 264).take 8).map encodePort

theorem portsSlice264 : (ports.drop 264).take 8 = (sourcePorts.drop 264).take 8 :=
  portsView264.trans (portsPiece264.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.program encodePort 264 8))

numeric_data_binding portsView272 : (ports.drop 272).take 8 = (ports256.drop 16).take 8

numeric_data_binding portsPiece272 : (ports256.drop 16).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.program.drop 272).take 8).map encodePort

theorem portsSlice272 : (ports.drop 272).take 8 = (sourcePorts.drop 272).take 8 :=
  portsView272.trans (portsPiece272.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.program encodePort 272 8))

numeric_data_binding portsView280 : (ports.drop 280).take 8 = (ports256.drop 24).take 8

numeric_data_binding portsPiece280 : (ports256.drop 24).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.program.drop 280).take 8).map encodePort

theorem portsSlice280 : (ports.drop 280).take 8 = (sourcePorts.drop 280).take 8 :=
  portsView280.trans (portsPiece280.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.program encodePort 280 8))

numeric_data_binding portsView288 : (ports.drop 288).take 8 = (ports288.drop 0).take 8

numeric_data_binding portsPiece288 : (ports288.drop 0).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.program.drop 288).take 8).map encodePort

theorem portsSlice288 : (ports.drop 288).take 8 = (sourcePorts.drop 288).take 8 :=
  portsView288.trans (portsPiece288.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.program encodePort 288 8))

numeric_data_binding portsView296 : (ports.drop 296).take 8 = (ports288.drop 8).take 8

numeric_data_binding portsPiece296 : (ports288.drop 8).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.program.drop 296).take 8).map encodePort

theorem portsSlice296 : (ports.drop 296).take 8 = (sourcePorts.drop 296).take 8 :=
  portsView296.trans (portsPiece296.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.program encodePort 296 8))

numeric_data_binding portsView304 : (ports.drop 304).take 8 = (ports288.drop 16).take 8

numeric_data_binding portsPiece304 : (ports288.drop 16).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.program.drop 304).take 8).map encodePort

theorem portsSlice304 : (ports.drop 304).take 8 = (sourcePorts.drop 304).take 8 :=
  portsView304.trans (portsPiece304.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.program encodePort 304 8))

numeric_data_binding portsView312 : (ports.drop 312).take 8 = (ports288.drop 24).take 8

numeric_data_binding portsPiece312 : (ports288.drop 24).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.program.drop 312).take 8).map encodePort

theorem portsSlice312 : (ports.drop 312).take 8 = (sourcePorts.drop 312).take 8 :=
  portsView312.trans (portsPiece312.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.program encodePort 312 8))

numeric_data_binding portsView320 : (ports.drop 320).take 8 = (ports320.drop 0).take 8

numeric_data_binding portsPiece320 : (ports320.drop 0).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.program.drop 320).take 8).map encodePort

theorem portsSlice320 : (ports.drop 320).take 8 = (sourcePorts.drop 320).take 8 :=
  portsView320.trans (portsPiece320.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.program encodePort 320 8))

numeric_data_binding portsView328 : (ports.drop 328).take 8 = (ports320.drop 8).take 8

numeric_data_binding portsPiece328 : (ports320.drop 8).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.program.drop 328).take 8).map encodePort

theorem portsSlice328 : (ports.drop 328).take 8 = (sourcePorts.drop 328).take 8 :=
  portsView328.trans (portsPiece328.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.program encodePort 328 8))

numeric_data_binding portsView336 : (ports.drop 336).take 8 = (ports320.drop 16).take 8

numeric_data_binding portsPiece336 : (ports320.drop 16).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.program.drop 336).take 8).map encodePort

theorem portsSlice336 : (ports.drop 336).take 8 = (sourcePorts.drop 336).take 8 :=
  portsView336.trans (portsPiece336.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.program encodePort 336 8))

numeric_data_binding portsView344 : (ports.drop 344).take 8 = (ports320.drop 24).take 8

numeric_data_binding portsPiece344 : (ports320.drop 24).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.program.drop 344).take 8).map encodePort

theorem portsSlice344 : (ports.drop 344).take 8 = (sourcePorts.drop 344).take 8 :=
  portsView344.trans (portsPiece344.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.program encodePort 344 8))

numeric_data_binding portsView352 : (ports.drop 352).take 8 = (ports352.drop 0).take 8

numeric_data_binding portsPiece352 : (ports352.drop 0).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.program.drop 352).take 8).map encodePort

theorem portsSlice352 : (ports.drop 352).take 8 = (sourcePorts.drop 352).take 8 :=
  portsView352.trans (portsPiece352.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.program encodePort 352 8))

numeric_data_binding portsView360 : (ports.drop 360).take 8 = (ports352.drop 8).take 8

numeric_data_binding portsPiece360 : (ports352.drop 8).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.program.drop 360).take 8).map encodePort

theorem portsSlice360 : (ports.drop 360).take 8 = (sourcePorts.drop 360).take 8 :=
  portsView360.trans (portsPiece360.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.program encodePort 360 8))

numeric_data_binding portsView368 : (ports.drop 368).take 8 = (ports352.drop 16).take 8

numeric_data_binding portsPiece368 : (ports352.drop 16).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.program.drop 368).take 8).map encodePort

theorem portsSlice368 : (ports.drop 368).take 8 = (sourcePorts.drop 368).take 8 :=
  portsView368.trans (portsPiece368.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.program encodePort 368 8))

numeric_data_binding portsView376 : (ports.drop 376).take 8 = (ports352.drop 24).take 8

numeric_data_binding portsPiece376 : (ports352.drop 24).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.program.drop 376).take 8).map encodePort

theorem portsSlice376 : (ports.drop 376).take 8 = (sourcePorts.drop 376).take 8 :=
  portsView376.trans (portsPiece376.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.program encodePort 376 8))

numeric_data_binding portsView384 : (ports.drop 384).take 8 = (ports384.drop 0).take 8

numeric_data_binding portsPiece384 : (ports384.drop 0).take 8 = ((Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.program.drop 384).take 8).map encodePort

theorem portsSlice384 : (ports.drop 384).take 8 = (sourcePorts.drop 384).take 8 :=
  portsView384.trans (portsPiece384.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.program encodePort 384 8))

numeric_data_binding portsView392 : (ports.drop 392).take 2 = (ports384.drop 8).take 2

numeric_data_binding portsPiece392 : (ports384.drop 8).take 2 = ((Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.program.drop 392).take 2).map encodePort

theorem portsSlice392 : (ports.drop 392).take 2 = (sourcePorts.drop 392).take 2 :=
  portsView392.trans (portsPiece392.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.program encodePort 392 2))

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

theorem portsNode168_16 : (ports.drop 168).take 16 = (sourcePorts.drop 168).take 16 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 168 8 8 portsSlice168 portsSlice176

theorem portsNode184_16 : (ports.drop 184).take 16 = (sourcePorts.drop 184).take 16 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 184 8 8 portsSlice184 portsSlice192

theorem portsNode168_32 : (ports.drop 168).take 32 = (sourcePorts.drop 168).take 32 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 168 16 16 portsNode168_16 portsNode184_16

theorem portsNode144_56 : (ports.drop 144).take 56 = (sourcePorts.drop 144).take 56 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 144 24 32 portsNode144_24 portsNode168_32

theorem portsNode96_104 : (ports.drop 96).take 104 = (sourcePorts.drop 96).take 104 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 96 48 56 portsNode96_48 portsNode144_56

theorem portsNode0_200 : (ports.drop 0).take 200 = (sourcePorts.drop 0).take 200 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 0 96 104 portsNode0_96 portsNode96_104

theorem portsNode208_16 : (ports.drop 208).take 16 = (sourcePorts.drop 208).take 16 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 208 8 8 portsSlice208 portsSlice216

theorem portsNode200_24 : (ports.drop 200).take 24 = (sourcePorts.drop 200).take 24 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 200 8 16 portsSlice200 portsNode208_16

theorem portsNode232_16 : (ports.drop 232).take 16 = (sourcePorts.drop 232).take 16 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 232 8 8 portsSlice232 portsSlice240

theorem portsNode224_24 : (ports.drop 224).take 24 = (sourcePorts.drop 224).take 24 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 224 8 16 portsSlice224 portsNode232_16

theorem portsNode200_48 : (ports.drop 200).take 48 = (sourcePorts.drop 200).take 48 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 200 24 24 portsNode200_24 portsNode224_24

theorem portsNode256_16 : (ports.drop 256).take 16 = (sourcePorts.drop 256).take 16 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 256 8 8 portsSlice256 portsSlice264

theorem portsNode248_24 : (ports.drop 248).take 24 = (sourcePorts.drop 248).take 24 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 248 8 16 portsSlice248 portsNode256_16

theorem portsNode280_16 : (ports.drop 280).take 16 = (sourcePorts.drop 280).take 16 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 280 8 8 portsSlice280 portsSlice288

theorem portsNode272_24 : (ports.drop 272).take 24 = (sourcePorts.drop 272).take 24 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 272 8 16 portsSlice272 portsNode280_16

theorem portsNode248_48 : (ports.drop 248).take 48 = (sourcePorts.drop 248).take 48 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 248 24 24 portsNode248_24 portsNode272_24

theorem portsNode200_96 : (ports.drop 200).take 96 = (sourcePorts.drop 200).take 96 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 200 48 48 portsNode200_48 portsNode248_48

theorem portsNode304_16 : (ports.drop 304).take 16 = (sourcePorts.drop 304).take 16 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 304 8 8 portsSlice304 portsSlice312

theorem portsNode296_24 : (ports.drop 296).take 24 = (sourcePorts.drop 296).take 24 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 296 8 16 portsSlice296 portsNode304_16

theorem portsNode328_16 : (ports.drop 328).take 16 = (sourcePorts.drop 328).take 16 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 328 8 8 portsSlice328 portsSlice336

theorem portsNode320_24 : (ports.drop 320).take 24 = (sourcePorts.drop 320).take 24 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 320 8 16 portsSlice320 portsNode328_16

theorem portsNode296_48 : (ports.drop 296).take 48 = (sourcePorts.drop 296).take 48 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 296 24 24 portsNode296_24 portsNode320_24

theorem portsNode352_16 : (ports.drop 352).take 16 = (sourcePorts.drop 352).take 16 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 352 8 8 portsSlice352 portsSlice360

theorem portsNode344_24 : (ports.drop 344).take 24 = (sourcePorts.drop 344).take 24 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 344 8 16 portsSlice344 portsNode352_16

theorem portsNode368_16 : (ports.drop 368).take 16 = (sourcePorts.drop 368).take 16 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 368 8 8 portsSlice368 portsSlice376

theorem portsNode384_10 : (ports.drop 384).take 10 = (sourcePorts.drop 384).take 10 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 384 8 2 portsSlice384 portsSlice392

theorem portsNode368_26 : (ports.drop 368).take 26 = (sourcePorts.drop 368).take 26 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 368 16 10 portsNode368_16 portsNode384_10

theorem portsNode344_50 : (ports.drop 344).take 50 = (sourcePorts.drop 344).take 50 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 344 24 26 portsNode344_24 portsNode368_26

theorem portsNode296_98 : (ports.drop 296).take 98 = (sourcePorts.drop 296).take 98 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 296 48 50 portsNode296_48 portsNode344_50

theorem portsNode200_194 : (ports.drop 200).take 194 = (sourcePorts.drop 200).take 194 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 200 96 98 portsNode200_96 portsNode296_98

theorem portsNode0_394 : (ports.drop 0).take 394 = (sourcePorts.drop 0).take 394 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 0 200 194 portsNode0_200 portsNode200_194

theorem programLength : Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.program.length = 394 := by decide +kernel

theorem ports_binding : ports = sourcePorts :=
  NumericQueryFrameChecks.complete_binding ports sourcePorts 394
    (by decide +kernel) (by rw [sourcePorts, List.length_map, programLength]) portsNode0_394

end Airbender.Compiler.FunctionalStepChecks.BlakeRoundUncached
