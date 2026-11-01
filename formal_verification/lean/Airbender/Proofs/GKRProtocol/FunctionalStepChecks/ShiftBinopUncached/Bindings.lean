import Airbender.Proofs.GKRProtocol.FunctionalStepChecks.ShiftBinopUncached.Data
import Airbender.Proofs.GKRProtocol.FunctionalNative.ShiftBinopUncachedFoundation
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.FunctionalStepChecks.ShiftBinopUncached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def encodePort (step : FunctionalStep) := NumericFunctionalStepChecks.encode Airbender.Compiler.FunctionalNative.ShiftBinopUncached.native.isBase ([], step)

noncomputable def sourcePorts := Airbender.Compiler.FunctionalNative.ShiftBinopUncached.native.program.map encodePort

numeric_data_binding portsView0 : (ports.drop 0).take 8 = (ports0.drop 0).take 8

numeric_data_binding portsPiece0 : (ports0.drop 0).take 8 = ((Airbender.Compiler.FunctionalNative.ShiftBinopUncached.native.program.drop 0).take 8).map encodePort

theorem portsSlice0 : (ports.drop 0).take 8 = (sourcePorts.drop 0).take 8 :=
  portsView0.trans (portsPiece0.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.ShiftBinopUncached.native.program encodePort 0 8))

numeric_data_binding portsView8 : (ports.drop 8).take 8 = (ports0.drop 8).take 8

numeric_data_binding portsPiece8 : (ports0.drop 8).take 8 = ((Airbender.Compiler.FunctionalNative.ShiftBinopUncached.native.program.drop 8).take 8).map encodePort

theorem portsSlice8 : (ports.drop 8).take 8 = (sourcePorts.drop 8).take 8 :=
  portsView8.trans (portsPiece8.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.ShiftBinopUncached.native.program encodePort 8 8))

numeric_data_binding portsView16 : (ports.drop 16).take 8 = (ports0.drop 16).take 8

numeric_data_binding portsPiece16 : (ports0.drop 16).take 8 = ((Airbender.Compiler.FunctionalNative.ShiftBinopUncached.native.program.drop 16).take 8).map encodePort

theorem portsSlice16 : (ports.drop 16).take 8 = (sourcePorts.drop 16).take 8 :=
  portsView16.trans (portsPiece16.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.ShiftBinopUncached.native.program encodePort 16 8))

numeric_data_binding portsView24 : (ports.drop 24).take 8 = (ports0.drop 24).take 8

numeric_data_binding portsPiece24 : (ports0.drop 24).take 8 = ((Airbender.Compiler.FunctionalNative.ShiftBinopUncached.native.program.drop 24).take 8).map encodePort

theorem portsSlice24 : (ports.drop 24).take 8 = (sourcePorts.drop 24).take 8 :=
  portsView24.trans (portsPiece24.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.ShiftBinopUncached.native.program encodePort 24 8))

numeric_data_binding portsView32 : (ports.drop 32).take 4 = (ports32.drop 0).take 4

numeric_data_binding portsPiece32 : (ports32.drop 0).take 4 = ((Airbender.Compiler.FunctionalNative.ShiftBinopUncached.native.program.drop 32).take 4).map encodePort

theorem portsSlice32 : (ports.drop 32).take 4 = (sourcePorts.drop 32).take 4 :=
  portsView32.trans (portsPiece32.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.ShiftBinopUncached.native.program encodePort 32 4))

theorem portsNode0_16 : (ports.drop 0).take 16 = (sourcePorts.drop 0).take 16 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 0 8 8 portsSlice0 portsSlice8

theorem portsNode24_12 : (ports.drop 24).take 12 = (sourcePorts.drop 24).take 12 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 24 8 4 portsSlice24 portsSlice32

theorem portsNode16_20 : (ports.drop 16).take 20 = (sourcePorts.drop 16).take 20 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 16 8 12 portsSlice16 portsNode24_12

theorem portsNode0_36 : (ports.drop 0).take 36 = (sourcePorts.drop 0).take 36 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 0 16 20 portsNode0_16 portsNode16_20

theorem programLength : Airbender.Compiler.FunctionalNative.ShiftBinopUncached.native.program.length = 36 := by decide +kernel

theorem ports_binding : ports = sourcePorts :=
  NumericQueryFrameChecks.complete_binding ports sourcePorts 36
    (by decide +kernel) (by rw [sourcePorts, List.length_map, programLength]) portsNode0_36

end Airbender.Compiler.FunctionalStepChecks.ShiftBinopUncached
