import Airbender.Proofs.GKRProtocol.FunctionalStepChecks.SubwordMemoryUncached.Data
import Airbender.Proofs.GKRProtocol.FunctionalNative.SubwordMemoryUncachedFoundation
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.FunctionalStepChecks.SubwordMemoryUncached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def encodePort (step : FunctionalStep) := NumericFunctionalStepChecks.encode Airbender.Compiler.FunctionalNative.SubwordMemoryUncached.native.isBase ([], step)

noncomputable def sourcePorts := Airbender.Compiler.FunctionalNative.SubwordMemoryUncached.native.program.map encodePort

numeric_data_binding portsView0 : (ports.drop 0).take 8 = (ports0.drop 0).take 8

numeric_data_binding portsPiece0 : (ports0.drop 0).take 8 = ((Airbender.Compiler.FunctionalNative.SubwordMemoryUncached.native.program.drop 0).take 8).map encodePort

theorem portsSlice0 : (ports.drop 0).take 8 = (sourcePorts.drop 0).take 8 :=
  portsView0.trans (portsPiece0.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.SubwordMemoryUncached.native.program encodePort 0 8))

numeric_data_binding portsView8 : (ports.drop 8).take 8 = (ports0.drop 8).take 8

numeric_data_binding portsPiece8 : (ports0.drop 8).take 8 = ((Airbender.Compiler.FunctionalNative.SubwordMemoryUncached.native.program.drop 8).take 8).map encodePort

theorem portsSlice8 : (ports.drop 8).take 8 = (sourcePorts.drop 8).take 8 :=
  portsView8.trans (portsPiece8.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.SubwordMemoryUncached.native.program encodePort 8 8))

numeric_data_binding portsView16 : (ports.drop 16).take 8 = (ports0.drop 16).take 8

numeric_data_binding portsPiece16 : (ports0.drop 16).take 8 = ((Airbender.Compiler.FunctionalNative.SubwordMemoryUncached.native.program.drop 16).take 8).map encodePort

theorem portsSlice16 : (ports.drop 16).take 8 = (sourcePorts.drop 16).take 8 :=
  portsView16.trans (portsPiece16.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.SubwordMemoryUncached.native.program encodePort 16 8))

numeric_data_binding portsView24 : (ports.drop 24).take 8 = (ports0.drop 24).take 8

numeric_data_binding portsPiece24 : (ports0.drop 24).take 8 = ((Airbender.Compiler.FunctionalNative.SubwordMemoryUncached.native.program.drop 24).take 8).map encodePort

theorem portsSlice24 : (ports.drop 24).take 8 = (sourcePorts.drop 24).take 8 :=
  portsView24.trans (portsPiece24.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.SubwordMemoryUncached.native.program encodePort 24 8))

numeric_data_binding portsView32 : (ports.drop 32).take 2 = (ports32.drop 0).take 2

numeric_data_binding portsPiece32 : (ports32.drop 0).take 2 = ((Airbender.Compiler.FunctionalNative.SubwordMemoryUncached.native.program.drop 32).take 2).map encodePort

theorem portsSlice32 : (ports.drop 32).take 2 = (sourcePorts.drop 32).take 2 :=
  portsView32.trans (portsPiece32.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.SubwordMemoryUncached.native.program encodePort 32 2))

theorem portsNode0_16 : (ports.drop 0).take 16 = (sourcePorts.drop 0).take 16 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 0 8 8 portsSlice0 portsSlice8

theorem portsNode24_10 : (ports.drop 24).take 10 = (sourcePorts.drop 24).take 10 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 24 8 2 portsSlice24 portsSlice32

theorem portsNode16_18 : (ports.drop 16).take 18 = (sourcePorts.drop 16).take 18 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 16 8 10 portsSlice16 portsNode24_10

theorem portsNode0_34 : (ports.drop 0).take 34 = (sourcePorts.drop 0).take 34 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 0 16 18 portsNode0_16 portsNode16_18

theorem programLength : Airbender.Compiler.FunctionalNative.SubwordMemoryUncached.native.program.length = 34 := by decide +kernel

theorem ports_binding : ports = sourcePorts :=
  NumericQueryFrameChecks.complete_binding ports sourcePorts 34
    (by decide +kernel) (by rw [sourcePorts, List.length_map, programLength]) portsNode0_34

end Airbender.Compiler.FunctionalStepChecks.SubwordMemoryUncached
