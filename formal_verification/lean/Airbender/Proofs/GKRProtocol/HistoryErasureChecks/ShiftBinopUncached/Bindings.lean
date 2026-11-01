import Airbender.Proofs.GKRProtocol.HistoryErasureChecks.ShiftBinopUncached.Data
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.HistoryErasureChecks.ShiftBinopUncached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

numeric_data_binding fast_binding : data = NumericHistoryErasureChecks.ofSource Airbender.Compiler.HistoryErasureNative.ShiftBinopUncached.native.historyCells Airbender.Compiler.SourceContractNative.ShiftBinopUncached.native.originals Airbender.Compiler.SourceContractNative.ShiftBinopUncached.native.clock Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.helperPlacement (Airbender.Compiler.HistoryErasureNative.ShiftBinopUncached.native.protectedFields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.helperPlacement.memory))

theorem source_binding : data = NumericHistoryErasureChecks.ofTyped Airbender.Compiler.HistoryErasureNative.ShiftBinopUncached.native.historyCells Airbender.Compiler.SourceContractNative.ShiftBinopUncached.native.protectedPolynomials (Airbender.Compiler.HistoryErasureNative.ShiftBinopUncached.native.protectedFields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.helperPlacement.memory)) := by
  have actual := fast_binding.trans (NumericHistoryErasureChecks.ofSource_eq Airbender.Compiler.HistoryErasureNative.ShiftBinopUncached.native.historyCells
    Airbender.Compiler.SourceContractNative.ShiftBinopUncached.native.originals Airbender.Compiler.SourceContractNative.ShiftBinopUncached.native.clock Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.helperPlacement (Airbender.Compiler.HistoryErasureNative.ShiftBinopUncached.native.protectedFields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.helperPlacement.memory)))
  simpa only [Airbender.Compiler.SourceContractNative.ShiftBinopUncached.native.protectedPolynomials, Airbender.Compiler.SourceContractNative.ShiftBinopUncached.native.clockPolynomials] using actual

end Airbender.Compiler.HistoryErasureChecks.ShiftBinopUncached
