import Airbender.Proofs.GKRProtocol.FunctionalStepChecks.ShiftBinopCached.Data
import Airbender.Proofs.GKRProtocol.FunctionalNative.ShiftBinopCachedFoundation
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.FunctionalStepChecks.ShiftBinopCached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def encodePort (step : FunctionalStep) := NumericFunctionalStepChecks.encode Airbender.Compiler.FunctionalNative.ShiftBinopCached.native.isBase ([], step)

noncomputable def sourcePorts := Airbender.Compiler.FunctionalNative.ShiftBinopCached.native.program.map encodePort

numeric_data_binding portsView0 : (ports.drop 0).take 8 = (ports0.drop 0).take 8

numeric_data_binding portsPiece0 : (ports0.drop 0).take 8 = ((Airbender.Compiler.FunctionalNative.ShiftBinopCached.native.program.drop 0).take 8).map encodePort

theorem portsSlice0 : (ports.drop 0).take 8 = (sourcePorts.drop 0).take 8 :=
  portsView0.trans (portsPiece0.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.ShiftBinopCached.native.program encodePort 0 8))

numeric_data_binding portsView8 : (ports.drop 8).take 8 = (ports0.drop 8).take 8

numeric_data_binding portsPiece8 : (ports0.drop 8).take 8 = ((Airbender.Compiler.FunctionalNative.ShiftBinopCached.native.program.drop 8).take 8).map encodePort

theorem portsSlice8 : (ports.drop 8).take 8 = (sourcePorts.drop 8).take 8 :=
  portsView8.trans (portsPiece8.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.ShiftBinopCached.native.program encodePort 8 8))

numeric_data_binding portsView16 : (ports.drop 16).take 8 = (ports0.drop 16).take 8

numeric_data_binding portsPiece16 : (ports0.drop 16).take 8 = ((Airbender.Compiler.FunctionalNative.ShiftBinopCached.native.program.drop 16).take 8).map encodePort

theorem portsSlice16 : (ports.drop 16).take 8 = (sourcePorts.drop 16).take 8 :=
  portsView16.trans (portsPiece16.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.ShiftBinopCached.native.program encodePort 16 8))

numeric_data_binding portsView24 : (ports.drop 24).take 8 = (ports0.drop 24).take 8

numeric_data_binding portsPiece24 : (ports0.drop 24).take 8 = ((Airbender.Compiler.FunctionalNative.ShiftBinopCached.native.program.drop 24).take 8).map encodePort

theorem portsSlice24 : (ports.drop 24).take 8 = (sourcePorts.drop 24).take 8 :=
  portsView24.trans (portsPiece24.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.ShiftBinopCached.native.program encodePort 24 8))

numeric_data_binding portsView32 : (ports.drop 32).take 8 = (ports32.drop 0).take 8

numeric_data_binding portsPiece32 : (ports32.drop 0).take 8 = ((Airbender.Compiler.FunctionalNative.ShiftBinopCached.native.program.drop 32).take 8).map encodePort

theorem portsSlice32 : (ports.drop 32).take 8 = (sourcePorts.drop 32).take 8 :=
  portsView32.trans (portsPiece32.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.ShiftBinopCached.native.program encodePort 32 8))

numeric_data_binding portsView40 : (ports.drop 40).take 8 = (ports32.drop 8).take 8

numeric_data_binding portsPiece40 : (ports32.drop 8).take 8 = ((Airbender.Compiler.FunctionalNative.ShiftBinopCached.native.program.drop 40).take 8).map encodePort

theorem portsSlice40 : (ports.drop 40).take 8 = (sourcePorts.drop 40).take 8 :=
  portsView40.trans (portsPiece40.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.ShiftBinopCached.native.program encodePort 40 8))

numeric_data_binding portsView48 : (ports.drop 48).take 3 = (ports32.drop 16).take 3

numeric_data_binding portsPiece48 : (ports32.drop 16).take 3 = ((Airbender.Compiler.FunctionalNative.ShiftBinopCached.native.program.drop 48).take 3).map encodePort

theorem portsSlice48 : (ports.drop 48).take 3 = (sourcePorts.drop 48).take 3 :=
  portsView48.trans (portsPiece48.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.ShiftBinopCached.native.program encodePort 48 3))

theorem portsNode8_16 : (ports.drop 8).take 16 = (sourcePorts.drop 8).take 16 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 8 8 8 portsSlice8 portsSlice16

theorem portsNode0_24 : (ports.drop 0).take 24 = (sourcePorts.drop 0).take 24 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 0 8 16 portsSlice0 portsNode8_16

theorem portsNode24_16 : (ports.drop 24).take 16 = (sourcePorts.drop 24).take 16 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 24 8 8 portsSlice24 portsSlice32

theorem portsNode40_11 : (ports.drop 40).take 11 = (sourcePorts.drop 40).take 11 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 40 8 3 portsSlice40 portsSlice48

theorem portsNode24_27 : (ports.drop 24).take 27 = (sourcePorts.drop 24).take 27 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 24 16 11 portsNode24_16 portsNode40_11

theorem portsNode0_51 : (ports.drop 0).take 51 = (sourcePorts.drop 0).take 51 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 0 24 27 portsNode0_24 portsNode24_27

theorem programLength : Airbender.Compiler.FunctionalNative.ShiftBinopCached.native.program.length = 51 := by decide +kernel

theorem ports_binding : ports = sourcePorts :=
  NumericQueryFrameChecks.complete_binding ports sourcePorts 51
    (by decide +kernel) (by rw [sourcePorts, List.length_map, programLength]) portsNode0_51

end Airbender.Compiler.FunctionalStepChecks.ShiftBinopCached
