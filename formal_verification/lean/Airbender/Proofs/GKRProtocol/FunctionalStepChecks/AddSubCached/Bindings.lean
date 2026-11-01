import Airbender.Proofs.GKRProtocol.FunctionalStepChecks.AddSubCached.Data
import Airbender.Proofs.GKRProtocol.FunctionalNative.AddSubCachedFoundation
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.FunctionalStepChecks.AddSubCached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def encodePort (step : FunctionalStep) := NumericFunctionalStepChecks.encode Airbender.Compiler.FunctionalNative.AddSubCached.native.isBase ([], step)

noncomputable def sourcePorts := Airbender.Compiler.FunctionalNative.AddSubCached.native.program.map encodePort

numeric_data_binding portsView0 : (ports.drop 0).take 8 = (ports0.drop 0).take 8

numeric_data_binding portsPiece0 : (ports0.drop 0).take 8 = ((Airbender.Compiler.FunctionalNative.AddSubCached.native.program.drop 0).take 8).map encodePort

theorem portsSlice0 : (ports.drop 0).take 8 = (sourcePorts.drop 0).take 8 :=
  portsView0.trans (portsPiece0.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.AddSubCached.native.program encodePort 0 8))

numeric_data_binding portsView8 : (ports.drop 8).take 8 = (ports0.drop 8).take 8

numeric_data_binding portsPiece8 : (ports0.drop 8).take 8 = ((Airbender.Compiler.FunctionalNative.AddSubCached.native.program.drop 8).take 8).map encodePort

theorem portsSlice8 : (ports.drop 8).take 8 = (sourcePorts.drop 8).take 8 :=
  portsView8.trans (portsPiece8.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.AddSubCached.native.program encodePort 8 8))

numeric_data_binding portsView16 : (ports.drop 16).take 8 = (ports0.drop 16).take 8

numeric_data_binding portsPiece16 : (ports0.drop 16).take 8 = ((Airbender.Compiler.FunctionalNative.AddSubCached.native.program.drop 16).take 8).map encodePort

theorem portsSlice16 : (ports.drop 16).take 8 = (sourcePorts.drop 16).take 8 :=
  portsView16.trans (portsPiece16.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.AddSubCached.native.program encodePort 16 8))

numeric_data_binding portsView24 : (ports.drop 24).take 8 = (ports0.drop 24).take 8

numeric_data_binding portsPiece24 : (ports0.drop 24).take 8 = ((Airbender.Compiler.FunctionalNative.AddSubCached.native.program.drop 24).take 8).map encodePort

theorem portsSlice24 : (ports.drop 24).take 8 = (sourcePorts.drop 24).take 8 :=
  portsView24.trans (portsPiece24.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.AddSubCached.native.program encodePort 24 8))

numeric_data_binding portsView32 : (ports.drop 32).take 8 = (ports32.drop 0).take 8

numeric_data_binding portsPiece32 : (ports32.drop 0).take 8 = ((Airbender.Compiler.FunctionalNative.AddSubCached.native.program.drop 32).take 8).map encodePort

theorem portsSlice32 : (ports.drop 32).take 8 = (sourcePorts.drop 32).take 8 :=
  portsView32.trans (portsPiece32.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.AddSubCached.native.program encodePort 32 8))

numeric_data_binding portsView40 : (ports.drop 40).take 7 = (ports32.drop 8).take 7

numeric_data_binding portsPiece40 : (ports32.drop 8).take 7 = ((Airbender.Compiler.FunctionalNative.AddSubCached.native.program.drop 40).take 7).map encodePort

theorem portsSlice40 : (ports.drop 40).take 7 = (sourcePorts.drop 40).take 7 :=
  portsView40.trans (portsPiece40.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.AddSubCached.native.program encodePort 40 7))

theorem portsNode8_16 : (ports.drop 8).take 16 = (sourcePorts.drop 8).take 16 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 8 8 8 portsSlice8 portsSlice16

theorem portsNode0_24 : (ports.drop 0).take 24 = (sourcePorts.drop 0).take 24 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 0 8 16 portsSlice0 portsNode8_16

theorem portsNode32_15 : (ports.drop 32).take 15 = (sourcePorts.drop 32).take 15 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 32 8 7 portsSlice32 portsSlice40

theorem portsNode24_23 : (ports.drop 24).take 23 = (sourcePorts.drop 24).take 23 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 24 8 15 portsSlice24 portsNode32_15

theorem portsNode0_47 : (ports.drop 0).take 47 = (sourcePorts.drop 0).take 47 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 0 24 23 portsNode0_24 portsNode24_23

theorem programLength : Airbender.Compiler.FunctionalNative.AddSubCached.native.program.length = 47 := by decide +kernel

theorem ports_binding : ports = sourcePorts :=
  NumericQueryFrameChecks.complete_binding ports sourcePorts 47
    (by decide +kernel) (by rw [sourcePorts, List.length_map, programLength]) portsNode0_47

end Airbender.Compiler.FunctionalStepChecks.AddSubCached
