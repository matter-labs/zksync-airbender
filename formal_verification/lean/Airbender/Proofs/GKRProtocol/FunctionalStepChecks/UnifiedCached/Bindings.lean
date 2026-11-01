import Airbender.Proofs.GKRProtocol.FunctionalStepChecks.UnifiedCached.Data
import Airbender.Proofs.GKRProtocol.FunctionalNative.UnifiedCachedFoundation
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.FunctionalStepChecks.UnifiedCached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def encodePort (step : FunctionalStep) := NumericFunctionalStepChecks.encode Airbender.Compiler.FunctionalNative.UnifiedCached.native.isBase ([], step)

noncomputable def sourcePorts := Airbender.Compiler.FunctionalNative.UnifiedCached.native.program.map encodePort

numeric_data_binding portsView0 : (ports.drop 0).take 8 = (ports0.drop 0).take 8

numeric_data_binding portsPiece0 : (ports0.drop 0).take 8 = ((Airbender.Compiler.FunctionalNative.UnifiedCached.native.program.drop 0).take 8).map encodePort

theorem portsSlice0 : (ports.drop 0).take 8 = (sourcePorts.drop 0).take 8 :=
  portsView0.trans (portsPiece0.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.UnifiedCached.native.program encodePort 0 8))

numeric_data_binding portsView8 : (ports.drop 8).take 8 = (ports0.drop 8).take 8

numeric_data_binding portsPiece8 : (ports0.drop 8).take 8 = ((Airbender.Compiler.FunctionalNative.UnifiedCached.native.program.drop 8).take 8).map encodePort

theorem portsSlice8 : (ports.drop 8).take 8 = (sourcePorts.drop 8).take 8 :=
  portsView8.trans (portsPiece8.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.UnifiedCached.native.program encodePort 8 8))

numeric_data_binding portsView16 : (ports.drop 16).take 8 = (ports0.drop 16).take 8

numeric_data_binding portsPiece16 : (ports0.drop 16).take 8 = ((Airbender.Compiler.FunctionalNative.UnifiedCached.native.program.drop 16).take 8).map encodePort

theorem portsSlice16 : (ports.drop 16).take 8 = (sourcePorts.drop 16).take 8 :=
  portsView16.trans (portsPiece16.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.UnifiedCached.native.program encodePort 16 8))

numeric_data_binding portsView24 : (ports.drop 24).take 8 = (ports0.drop 24).take 8

numeric_data_binding portsPiece24 : (ports0.drop 24).take 8 = ((Airbender.Compiler.FunctionalNative.UnifiedCached.native.program.drop 24).take 8).map encodePort

theorem portsSlice24 : (ports.drop 24).take 8 = (sourcePorts.drop 24).take 8 :=
  portsView24.trans (portsPiece24.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.UnifiedCached.native.program encodePort 24 8))

numeric_data_binding portsView32 : (ports.drop 32).take 8 = (ports32.drop 0).take 8

numeric_data_binding portsPiece32 : (ports32.drop 0).take 8 = ((Airbender.Compiler.FunctionalNative.UnifiedCached.native.program.drop 32).take 8).map encodePort

theorem portsSlice32 : (ports.drop 32).take 8 = (sourcePorts.drop 32).take 8 :=
  portsView32.trans (portsPiece32.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.UnifiedCached.native.program encodePort 32 8))

numeric_data_binding portsView40 : (ports.drop 40).take 8 = (ports32.drop 8).take 8

numeric_data_binding portsPiece40 : (ports32.drop 8).take 8 = ((Airbender.Compiler.FunctionalNative.UnifiedCached.native.program.drop 40).take 8).map encodePort

theorem portsSlice40 : (ports.drop 40).take 8 = (sourcePorts.drop 40).take 8 :=
  portsView40.trans (portsPiece40.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.UnifiedCached.native.program encodePort 40 8))

numeric_data_binding portsView48 : (ports.drop 48).take 8 = (ports32.drop 16).take 8

numeric_data_binding portsPiece48 : (ports32.drop 16).take 8 = ((Airbender.Compiler.FunctionalNative.UnifiedCached.native.program.drop 48).take 8).map encodePort

theorem portsSlice48 : (ports.drop 48).take 8 = (sourcePorts.drop 48).take 8 :=
  portsView48.trans (portsPiece48.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.UnifiedCached.native.program encodePort 48 8))

numeric_data_binding portsView56 : (ports.drop 56).take 8 = (ports32.drop 24).take 8

numeric_data_binding portsPiece56 : (ports32.drop 24).take 8 = ((Airbender.Compiler.FunctionalNative.UnifiedCached.native.program.drop 56).take 8).map encodePort

theorem portsSlice56 : (ports.drop 56).take 8 = (sourcePorts.drop 56).take 8 :=
  portsView56.trans (portsPiece56.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.UnifiedCached.native.program encodePort 56 8))

numeric_data_binding portsView64 : (ports.drop 64).take 2 = (ports64.drop 0).take 2

numeric_data_binding portsPiece64 : (ports64.drop 0).take 2 = ((Airbender.Compiler.FunctionalNative.UnifiedCached.native.program.drop 64).take 2).map encodePort

theorem portsSlice64 : (ports.drop 64).take 2 = (sourcePorts.drop 64).take 2 :=
  portsView64.trans (portsPiece64.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.UnifiedCached.native.program encodePort 64 2))

theorem portsNode0_16 : (ports.drop 0).take 16 = (sourcePorts.drop 0).take 16 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 0 8 8 portsSlice0 portsSlice8

theorem portsNode16_16 : (ports.drop 16).take 16 = (sourcePorts.drop 16).take 16 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 16 8 8 portsSlice16 portsSlice24

theorem portsNode0_32 : (ports.drop 0).take 32 = (sourcePorts.drop 0).take 32 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 0 16 16 portsNode0_16 portsNode16_16

theorem portsNode32_16 : (ports.drop 32).take 16 = (sourcePorts.drop 32).take 16 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 32 8 8 portsSlice32 portsSlice40

theorem portsNode56_10 : (ports.drop 56).take 10 = (sourcePorts.drop 56).take 10 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 56 8 2 portsSlice56 portsSlice64

theorem portsNode48_18 : (ports.drop 48).take 18 = (sourcePorts.drop 48).take 18 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 48 8 10 portsSlice48 portsNode56_10

theorem portsNode32_34 : (ports.drop 32).take 34 = (sourcePorts.drop 32).take 34 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 32 16 18 portsNode32_16 portsNode48_18

theorem portsNode0_66 : (ports.drop 0).take 66 = (sourcePorts.drop 0).take 66 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 0 32 34 portsNode0_32 portsNode32_34

theorem programLength : Airbender.Compiler.FunctionalNative.UnifiedCached.native.program.length = 66 := by decide +kernel

theorem ports_binding : ports = sourcePorts :=
  NumericQueryFrameChecks.complete_binding ports sourcePorts 66
    (by decide +kernel) (by rw [sourcePorts, List.length_map, programLength]) portsNode0_66

end Airbender.Compiler.FunctionalStepChecks.UnifiedCached
