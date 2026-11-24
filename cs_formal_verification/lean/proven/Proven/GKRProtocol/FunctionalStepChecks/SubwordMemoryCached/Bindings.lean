module
import all Mathlib.Data.List.Sort
public import Proven.GKRProtocol.FunctionalStepChecks.SubwordMemoryCached.Data
public import Proven.GKRProtocol.FunctionalNative.SubwordMemoryCachedFoundation
public import Proven.GKRProtocol.NumericQueryFrameBindings
public import Proven.Import.GKRProtocol.NumericArithmeticDataImport

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.FunctionalStepChecks.SubwordMemoryCached
open Airbender.Compiler
set_option maxRecDepth 8192

noncomputable def encodePort (step : FunctionalStep) := NumericFunctionalStepChecks.encode Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.isBase ([], step)

noncomputable def sourcePorts := Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.program.map encodePort

numeric_data_binding portsView0 : (ports.drop 0).take 8 = (ports0.drop 0).take 8

numeric_data_binding portsPiece0 : (ports0.drop 0).take 8 = ((Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.program.drop 0).take 8).map encodePort

theorem portsSlice0 : (ports.drop 0).take 8 = (sourcePorts.drop 0).take 8 :=
  portsView0.trans (portsPiece0.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.program encodePort 0 8))

numeric_data_binding portsView8 : (ports.drop 8).take 8 = (ports0.drop 8).take 8

numeric_data_binding portsPiece8 : (ports0.drop 8).take 8 = ((Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.program.drop 8).take 8).map encodePort

theorem portsSlice8 : (ports.drop 8).take 8 = (sourcePorts.drop 8).take 8 :=
  portsView8.trans (portsPiece8.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.program encodePort 8 8))

numeric_data_binding portsView16 : (ports.drop 16).take 8 = (ports0.drop 16).take 8

numeric_data_binding portsPiece16 : (ports0.drop 16).take 8 = ((Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.program.drop 16).take 8).map encodePort

theorem portsSlice16 : (ports.drop 16).take 8 = (sourcePorts.drop 16).take 8 :=
  portsView16.trans (portsPiece16.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.program encodePort 16 8))

numeric_data_binding portsView24 : (ports.drop 24).take 8 = (ports0.drop 24).take 8

numeric_data_binding portsPiece24 : (ports0.drop 24).take 8 = ((Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.program.drop 24).take 8).map encodePort

theorem portsSlice24 : (ports.drop 24).take 8 = (sourcePorts.drop 24).take 8 :=
  portsView24.trans (portsPiece24.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.program encodePort 24 8))

numeric_data_binding portsView32 : (ports.drop 32).take 8 = (ports32.drop 0).take 8

numeric_data_binding portsPiece32 : (ports32.drop 0).take 8 = ((Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.program.drop 32).take 8).map encodePort

theorem portsSlice32 : (ports.drop 32).take 8 = (sourcePorts.drop 32).take 8 :=
  portsView32.trans (portsPiece32.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.program encodePort 32 8))

numeric_data_binding portsView40 : (ports.drop 40).take 6 = (ports32.drop 8).take 6

numeric_data_binding portsPiece40 : (ports32.drop 8).take 6 = ((Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.program.drop 40).take 6).map encodePort

theorem portsSlice40 : (ports.drop 40).take 6 = (sourcePorts.drop 40).take 6 :=
  portsView40.trans (portsPiece40.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.program encodePort 40 6))

theorem portsNode8_16 : (ports.drop 8).take 16 = (sourcePorts.drop 8).take 16 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 8 8 8 portsSlice8 portsSlice16

theorem portsNode0_24 : (ports.drop 0).take 24 = (sourcePorts.drop 0).take 24 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 0 8 16 portsSlice0 portsNode8_16

theorem portsNode32_14 : (ports.drop 32).take 14 = (sourcePorts.drop 32).take 14 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 32 8 6 portsSlice32 portsSlice40

theorem portsNode24_22 : (ports.drop 24).take 22 = (sourcePorts.drop 24).take 22 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 24 8 14 portsSlice24 portsNode32_14

theorem portsNode0_46 : (ports.drop 0).take 46 = (sourcePorts.drop 0).take 46 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 0 24 22 portsNode0_24 portsNode24_22

theorem programLength : Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.program.length = 46 := by decide +kernel

theorem ports_binding : ports = sourcePorts :=
  NumericQueryFrameChecks.complete_binding ports sourcePorts 46
    (by decide +kernel) (by rw [sourcePorts, List.length_map, programLength]) portsNode0_46

end Airbender.Compiler.FunctionalStepChecks.SubwordMemoryCached
