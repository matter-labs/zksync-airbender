import Airbender.Proofs.GKRProtocol.FunctionalStepChecks.KeccakUncached.Data
import Airbender.Proofs.GKRProtocol.FunctionalNative.KeccakUncachedFoundation
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.FunctionalStepChecks.KeccakUncached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def encodePort (step : FunctionalStep) := NumericFunctionalStepChecks.encode Airbender.Compiler.FunctionalNative.KeccakUncached.native.isBase ([], step)

noncomputable def sourcePorts := Airbender.Compiler.FunctionalNative.KeccakUncached.native.program.map encodePort

numeric_data_binding portsView0 : (ports.drop 0).take 8 = (ports0.drop 0).take 8

numeric_data_binding portsPiece0 : (ports0.drop 0).take 8 = ((Airbender.Compiler.FunctionalNative.KeccakUncached.native.program.drop 0).take 8).map encodePort

theorem portsSlice0 : (ports.drop 0).take 8 = (sourcePorts.drop 0).take 8 :=
  portsView0.trans (portsPiece0.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.KeccakUncached.native.program encodePort 0 8))

numeric_data_binding portsView8 : (ports.drop 8).take 8 = (ports0.drop 8).take 8

numeric_data_binding portsPiece8 : (ports0.drop 8).take 8 = ((Airbender.Compiler.FunctionalNative.KeccakUncached.native.program.drop 8).take 8).map encodePort

theorem portsSlice8 : (ports.drop 8).take 8 = (sourcePorts.drop 8).take 8 :=
  portsView8.trans (portsPiece8.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.KeccakUncached.native.program encodePort 8 8))

numeric_data_binding portsView16 : (ports.drop 16).take 8 = (ports0.drop 16).take 8

numeric_data_binding portsPiece16 : (ports0.drop 16).take 8 = ((Airbender.Compiler.FunctionalNative.KeccakUncached.native.program.drop 16).take 8).map encodePort

theorem portsSlice16 : (ports.drop 16).take 8 = (sourcePorts.drop 16).take 8 :=
  portsView16.trans (portsPiece16.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.KeccakUncached.native.program encodePort 16 8))

numeric_data_binding portsView24 : (ports.drop 24).take 8 = (ports0.drop 24).take 8

numeric_data_binding portsPiece24 : (ports0.drop 24).take 8 = ((Airbender.Compiler.FunctionalNative.KeccakUncached.native.program.drop 24).take 8).map encodePort

theorem portsSlice24 : (ports.drop 24).take 8 = (sourcePorts.drop 24).take 8 :=
  portsView24.trans (portsPiece24.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.KeccakUncached.native.program encodePort 24 8))

numeric_data_binding portsView32 : (ports.drop 32).take 8 = (ports32.drop 0).take 8

numeric_data_binding portsPiece32 : (ports32.drop 0).take 8 = ((Airbender.Compiler.FunctionalNative.KeccakUncached.native.program.drop 32).take 8).map encodePort

theorem portsSlice32 : (ports.drop 32).take 8 = (sourcePorts.drop 32).take 8 :=
  portsView32.trans (portsPiece32.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.KeccakUncached.native.program encodePort 32 8))

numeric_data_binding portsView40 : (ports.drop 40).take 8 = (ports32.drop 8).take 8

numeric_data_binding portsPiece40 : (ports32.drop 8).take 8 = ((Airbender.Compiler.FunctionalNative.KeccakUncached.native.program.drop 40).take 8).map encodePort

theorem portsSlice40 : (ports.drop 40).take 8 = (sourcePorts.drop 40).take 8 :=
  portsView40.trans (portsPiece40.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.KeccakUncached.native.program encodePort 40 8))

numeric_data_binding portsView48 : (ports.drop 48).take 8 = (ports32.drop 16).take 8

numeric_data_binding portsPiece48 : (ports32.drop 16).take 8 = ((Airbender.Compiler.FunctionalNative.KeccakUncached.native.program.drop 48).take 8).map encodePort

theorem portsSlice48 : (ports.drop 48).take 8 = (sourcePorts.drop 48).take 8 :=
  portsView48.trans (portsPiece48.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.KeccakUncached.native.program encodePort 48 8))

numeric_data_binding portsView56 : (ports.drop 56).take 8 = (ports32.drop 24).take 8

numeric_data_binding portsPiece56 : (ports32.drop 24).take 8 = ((Airbender.Compiler.FunctionalNative.KeccakUncached.native.program.drop 56).take 8).map encodePort

theorem portsSlice56 : (ports.drop 56).take 8 = (sourcePorts.drop 56).take 8 :=
  portsView56.trans (portsPiece56.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.KeccakUncached.native.program encodePort 56 8))

numeric_data_binding portsView64 : (ports.drop 64).take 8 = (ports64.drop 0).take 8

numeric_data_binding portsPiece64 : (ports64.drop 0).take 8 = ((Airbender.Compiler.FunctionalNative.KeccakUncached.native.program.drop 64).take 8).map encodePort

theorem portsSlice64 : (ports.drop 64).take 8 = (sourcePorts.drop 64).take 8 :=
  portsView64.trans (portsPiece64.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.KeccakUncached.native.program encodePort 64 8))

numeric_data_binding portsView72 : (ports.drop 72).take 8 = (ports64.drop 8).take 8

numeric_data_binding portsPiece72 : (ports64.drop 8).take 8 = ((Airbender.Compiler.FunctionalNative.KeccakUncached.native.program.drop 72).take 8).map encodePort

theorem portsSlice72 : (ports.drop 72).take 8 = (sourcePorts.drop 72).take 8 :=
  portsView72.trans (portsPiece72.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.KeccakUncached.native.program encodePort 72 8))

numeric_data_binding portsView80 : (ports.drop 80).take 8 = (ports64.drop 16).take 8

numeric_data_binding portsPiece80 : (ports64.drop 16).take 8 = ((Airbender.Compiler.FunctionalNative.KeccakUncached.native.program.drop 80).take 8).map encodePort

theorem portsSlice80 : (ports.drop 80).take 8 = (sourcePorts.drop 80).take 8 :=
  portsView80.trans (portsPiece80.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.KeccakUncached.native.program encodePort 80 8))

numeric_data_binding portsView88 : (ports.drop 88).take 8 = (ports64.drop 24).take 8

numeric_data_binding portsPiece88 : (ports64.drop 24).take 8 = ((Airbender.Compiler.FunctionalNative.KeccakUncached.native.program.drop 88).take 8).map encodePort

theorem portsSlice88 : (ports.drop 88).take 8 = (sourcePorts.drop 88).take 8 :=
  portsView88.trans (portsPiece88.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.KeccakUncached.native.program encodePort 88 8))

numeric_data_binding portsView96 : (ports.drop 96).take 8 = (ports96.drop 0).take 8

numeric_data_binding portsPiece96 : (ports96.drop 0).take 8 = ((Airbender.Compiler.FunctionalNative.KeccakUncached.native.program.drop 96).take 8).map encodePort

theorem portsSlice96 : (ports.drop 96).take 8 = (sourcePorts.drop 96).take 8 :=
  portsView96.trans (portsPiece96.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.KeccakUncached.native.program encodePort 96 8))

numeric_data_binding portsView104 : (ports.drop 104).take 8 = (ports96.drop 8).take 8

numeric_data_binding portsPiece104 : (ports96.drop 8).take 8 = ((Airbender.Compiler.FunctionalNative.KeccakUncached.native.program.drop 104).take 8).map encodePort

theorem portsSlice104 : (ports.drop 104).take 8 = (sourcePorts.drop 104).take 8 :=
  portsView104.trans (portsPiece104.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.KeccakUncached.native.program encodePort 104 8))

numeric_data_binding portsView112 : (ports.drop 112).take 1 = (ports96.drop 16).take 1

numeric_data_binding portsPiece112 : (ports96.drop 16).take 1 = ((Airbender.Compiler.FunctionalNative.KeccakUncached.native.program.drop 112).take 1).map encodePort

theorem portsSlice112 : (ports.drop 112).take 1 = (sourcePorts.drop 112).take 1 :=
  portsView112.trans (portsPiece112.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.FunctionalNative.KeccakUncached.native.program encodePort 112 1))

theorem portsNode8_16 : (ports.drop 8).take 16 = (sourcePorts.drop 8).take 16 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 8 8 8 portsSlice8 portsSlice16

theorem portsNode0_24 : (ports.drop 0).take 24 = (sourcePorts.drop 0).take 24 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 0 8 16 portsSlice0 portsNode8_16

theorem portsNode24_16 : (ports.drop 24).take 16 = (sourcePorts.drop 24).take 16 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 24 8 8 portsSlice24 portsSlice32

theorem portsNode40_16 : (ports.drop 40).take 16 = (sourcePorts.drop 40).take 16 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 40 8 8 portsSlice40 portsSlice48

theorem portsNode24_32 : (ports.drop 24).take 32 = (sourcePorts.drop 24).take 32 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 24 16 16 portsNode24_16 portsNode40_16

theorem portsNode0_56 : (ports.drop 0).take 56 = (sourcePorts.drop 0).take 56 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 0 24 32 portsNode0_24 portsNode24_32

theorem portsNode56_16 : (ports.drop 56).take 16 = (sourcePorts.drop 56).take 16 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 56 8 8 portsSlice56 portsSlice64

theorem portsNode72_16 : (ports.drop 72).take 16 = (sourcePorts.drop 72).take 16 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 72 8 8 portsSlice72 portsSlice80

theorem portsNode56_32 : (ports.drop 56).take 32 = (sourcePorts.drop 56).take 32 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 56 16 16 portsNode56_16 portsNode72_16

theorem portsNode88_16 : (ports.drop 88).take 16 = (sourcePorts.drop 88).take 16 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 88 8 8 portsSlice88 portsSlice96

theorem portsNode104_9 : (ports.drop 104).take 9 = (sourcePorts.drop 104).take 9 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 104 8 1 portsSlice104 portsSlice112

theorem portsNode88_25 : (ports.drop 88).take 25 = (sourcePorts.drop 88).take 25 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 88 16 9 portsNode88_16 portsNode104_9

theorem portsNode56_57 : (ports.drop 56).take 57 = (sourcePorts.drop 56).take 57 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 56 32 25 portsNode56_32 portsNode88_25

theorem portsNode0_113 : (ports.drop 0).take 113 = (sourcePorts.drop 0).take 113 :=
  NumericQueryFrameChecks.merge_bindings ports sourcePorts 0 56 57 portsNode0_56 portsNode56_57

theorem programLength : Airbender.Compiler.FunctionalNative.KeccakUncached.native.program.length = 113 := by decide +kernel

theorem ports_binding : ports = sourcePorts :=
  NumericQueryFrameChecks.complete_binding ports sourcePorts 113
    (by decide +kernel) (by rw [sourcePorts, List.length_map, programLength]) portsNode0_113

end Airbender.Compiler.FunctionalStepChecks.KeccakUncached
