import Airbender.Proofs.GKRProtocol.FunctionalStepChecks.WordMemoryUncached.Data
import Airbender.Proofs.GKRProtocol.FunctionalNative.WordMemoryUncachedFoundation
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.FunctionalStepChecks.WordMemoryUncached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def encodePort (step : FunctionalStep) := NumericFunctionalStepChecks.encode Airbender.Compiler.FunctionalNative.WordMemoryUncached.native.isBase ([], step)

noncomputable def sourcePorts := Airbender.Compiler.FunctionalNative.WordMemoryUncached.native.program.map encodePort

numeric_data_binding portsView0 : (ports.drop 0).take 8 = (ports0.drop 0).take 8

numeric_data_binding portsPiece0 : (ports0.drop 0).take 8 = ((Airbender.Compiler.FunctionalNative.WordMemoryUncached.native.program.drop 0).take 8).map encodePort

theorem portsSlice0 : (ports.drop 0).take 8 = (sourcePorts.drop 0).take 8 :=
  portsView0.trans (portsPiece0.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.WordMemoryUncached.native.program encodePort 0 8))

numeric_data_binding portsView8 : (ports.drop 8).take 8 = (ports0.drop 8).take 8

numeric_data_binding portsPiece8 : (ports0.drop 8).take 8 = ((Airbender.Compiler.FunctionalNative.WordMemoryUncached.native.program.drop 8).take 8).map encodePort

theorem portsSlice8 : (ports.drop 8).take 8 = (sourcePorts.drop 8).take 8 :=
  portsView8.trans (portsPiece8.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.WordMemoryUncached.native.program encodePort 8 8))

numeric_data_binding portsView16 : (ports.drop 16).take 8 = (ports0.drop 16).take 8

numeric_data_binding portsPiece16 : (ports0.drop 16).take 8 = ((Airbender.Compiler.FunctionalNative.WordMemoryUncached.native.program.drop 16).take 8).map encodePort

theorem portsSlice16 : (ports.drop 16).take 8 = (sourcePorts.drop 16).take 8 :=
  portsView16.trans (portsPiece16.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.WordMemoryUncached.native.program encodePort 16 8))

numeric_data_binding portsView24 : (ports.drop 24).take 8 = (ports0.drop 24).take 8

numeric_data_binding portsPiece24 : (ports0.drop 24).take 8 = ((Airbender.Compiler.FunctionalNative.WordMemoryUncached.native.program.drop 24).take 8).map encodePort

theorem portsSlice24 : (ports.drop 24).take 8 = (sourcePorts.drop 24).take 8 :=
  portsView24.trans (portsPiece24.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.WordMemoryUncached.native.program encodePort 24 8))

numeric_data_binding portsView32 : (ports.drop 32).take 1 = (ports32.drop 0).take 1

numeric_data_binding portsPiece32 : (ports32.drop 0).take 1 = ((Airbender.Compiler.FunctionalNative.WordMemoryUncached.native.program.drop 32).take 1).map encodePort

theorem portsSlice32 : (ports.drop 32).take 1 = (sourcePorts.drop 32).take 1 :=
  portsView32.trans (portsPiece32.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.WordMemoryUncached.native.program encodePort 32 1))

theorem portsNode0_16 : (ports.drop 0).take 16 = (sourcePorts.drop 0).take 16 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 0 8 8 portsSlice0 portsSlice8

theorem portsNode24_9 : (ports.drop 24).take 9 = (sourcePorts.drop 24).take 9 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 24 8 1 portsSlice24 portsSlice32

theorem portsNode16_17 : (ports.drop 16).take 17 = (sourcePorts.drop 16).take 17 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 16 8 9 portsSlice16 portsNode24_9

theorem portsNode0_33 : (ports.drop 0).take 33 = (sourcePorts.drop 0).take 33 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 0 16 17 portsNode0_16 portsNode16_17

theorem programLength : Airbender.Compiler.FunctionalNative.WordMemoryUncached.native.program.length = 33 := by decide +kernel

theorem ports_binding : ports = sourcePorts :=
  NumericQueryFrameChecks.complete_binding ports sourcePorts 33
    (by decide +kernel) (by rw [sourcePorts, List.length_map, programLength]) portsNode0_33

end Airbender.Compiler.FunctionalStepChecks.WordMemoryUncached
