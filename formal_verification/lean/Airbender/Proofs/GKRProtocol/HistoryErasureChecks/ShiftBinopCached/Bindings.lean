import Airbender.Proofs.GKRProtocol.HistoryErasureChecks.ShiftBinopCached.Data
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.HistoryErasureChecks.ShiftBinopCached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

numeric_data_binding fast_binding : data = NumericHistoryErasureChecks.ofSource Airbender.Compiler.HistoryErasureNative.ShiftBinopCached.native.historyCells Airbender.Compiler.SourceContractNative.ShiftBinopCached.native.originals Airbender.Compiler.SourceContractNative.ShiftBinopCached.native.clock Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.helperPlacement (Airbender.Compiler.HistoryErasureNative.ShiftBinopCached.native.protectedFields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.helperPlacement.memory))

theorem source_binding : data = NumericHistoryErasureChecks.ofTyped Airbender.Compiler.HistoryErasureNative.ShiftBinopCached.native.historyCells Airbender.Compiler.SourceContractNative.ShiftBinopCached.native.protectedPolynomials (Airbender.Compiler.HistoryErasureNative.ShiftBinopCached.native.protectedFields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.helperPlacement.memory)) := by
  have actual := fast_binding.trans (NumericHistoryErasureChecks.ofSource_eq Airbender.Compiler.HistoryErasureNative.ShiftBinopCached.native.historyCells
    Airbender.Compiler.SourceContractNative.ShiftBinopCached.native.originals Airbender.Compiler.SourceContractNative.ShiftBinopCached.native.clock Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.helperPlacement (Airbender.Compiler.HistoryErasureNative.ShiftBinopCached.native.protectedFields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.helperPlacement.memory)))
  simpa only [Airbender.Compiler.SourceContractNative.ShiftBinopCached.native.protectedPolynomials, Airbender.Compiler.SourceContractNative.ShiftBinopCached.native.clockPolynomials] using actual

end Airbender.Compiler.HistoryErasureChecks.ShiftBinopCached
