import Airbender.Proofs.GKRProtocol.FunctionalStepChecks.AddSubUncached.Data
import Airbender.Proofs.GKRProtocol.FunctionalNative.AddSubUncachedFoundation
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.FunctionalStepChecks.AddSubUncached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def encodePort (step : FunctionalStep) := NumericFunctionalStepChecks.encode Airbender.Compiler.FunctionalNative.AddSubUncached.native.isBase ([], step)

noncomputable def sourcePorts := Airbender.Compiler.FunctionalNative.AddSubUncached.native.program.map encodePort

numeric_data_binding portsView0 : (ports.drop 0).take 8 = (ports0.drop 0).take 8

numeric_data_binding portsPiece0 : (ports0.drop 0).take 8 = ((Airbender.Compiler.FunctionalNative.AddSubUncached.native.program.drop 0).take 8).map encodePort

theorem portsSlice0 : (ports.drop 0).take 8 = (sourcePorts.drop 0).take 8 :=
  portsView0.trans (portsPiece0.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.AddSubUncached.native.program encodePort 0 8))

numeric_data_binding portsView8 : (ports.drop 8).take 8 = (ports0.drop 8).take 8

numeric_data_binding portsPiece8 : (ports0.drop 8).take 8 = ((Airbender.Compiler.FunctionalNative.AddSubUncached.native.program.drop 8).take 8).map encodePort

theorem portsSlice8 : (ports.drop 8).take 8 = (sourcePorts.drop 8).take 8 :=
  portsView8.trans (portsPiece8.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.AddSubUncached.native.program encodePort 8 8))

numeric_data_binding portsView16 : (ports.drop 16).take 8 = (ports0.drop 16).take 8

numeric_data_binding portsPiece16 : (ports0.drop 16).take 8 = ((Airbender.Compiler.FunctionalNative.AddSubUncached.native.program.drop 16).take 8).map encodePort

theorem portsSlice16 : (ports.drop 16).take 8 = (sourcePorts.drop 16).take 8 :=
  portsView16.trans (portsPiece16.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.AddSubUncached.native.program encodePort 16 8))

numeric_data_binding portsView24 : (ports.drop 24).take 8 = (ports0.drop 24).take 8

numeric_data_binding portsPiece24 : (ports0.drop 24).take 8 = ((Airbender.Compiler.FunctionalNative.AddSubUncached.native.program.drop 24).take 8).map encodePort

theorem portsSlice24 : (ports.drop 24).take 8 = (sourcePorts.drop 24).take 8 :=
  portsView24.trans (portsPiece24.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.AddSubUncached.native.program encodePort 24 8))

numeric_data_binding portsView32 : (ports.drop 32).take 5 = (ports32.drop 0).take 5

numeric_data_binding portsPiece32 : (ports32.drop 0).take 5 = ((Airbender.Compiler.FunctionalNative.AddSubUncached.native.program.drop 32).take 5).map encodePort

theorem portsSlice32 : (ports.drop 32).take 5 = (sourcePorts.drop 32).take 5 :=
  portsView32.trans (portsPiece32.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.AddSubUncached.native.program encodePort 32 5))

theorem portsNode0_16 : (ports.drop 0).take 16 = (sourcePorts.drop 0).take 16 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 0 8 8 portsSlice0 portsSlice8

theorem portsNode24_13 : (ports.drop 24).take 13 = (sourcePorts.drop 24).take 13 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 24 8 5 portsSlice24 portsSlice32

theorem portsNode16_21 : (ports.drop 16).take 21 = (sourcePorts.drop 16).take 21 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 16 8 13 portsSlice16 portsNode24_13

theorem portsNode0_37 : (ports.drop 0).take 37 = (sourcePorts.drop 0).take 37 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 0 16 21 portsNode0_16 portsNode16_21

theorem programLength : Airbender.Compiler.FunctionalNative.AddSubUncached.native.program.length = 37 := by decide +kernel

theorem ports_binding : ports = sourcePorts :=
  NumericQueryFrameChecks.complete_binding ports sourcePorts 37
    (by decide +kernel) (by rw [sourcePorts, List.length_map, programLength]) portsNode0_37

end Airbender.Compiler.FunctionalStepChecks.AddSubUncached
