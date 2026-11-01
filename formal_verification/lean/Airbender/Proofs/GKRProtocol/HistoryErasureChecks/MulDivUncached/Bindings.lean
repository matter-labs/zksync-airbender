import Airbender.Proofs.GKRProtocol.HistoryErasureChecks.MulDivUncached.Data
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.HistoryErasureChecks.MulDivUncached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

numeric_data_binding fast_binding : data = NumericHistoryErasureChecks.ofSource Airbender.Compiler.HistoryErasureNative.MulDivUncached.native.historyCells Airbender.Compiler.SourceContractNative.MulDivUncached.native.originals Airbender.Compiler.SourceContractNative.MulDivUncached.native.clock Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.helperPlacement (Airbender.Compiler.HistoryErasureNative.MulDivUncached.native.protectedFields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.helperPlacement.memory))

theorem source_binding : data = NumericHistoryErasureChecks.ofTyped Airbender.Compiler.HistoryErasureNative.MulDivUncached.native.historyCells Airbender.Compiler.SourceContractNative.MulDivUncached.native.protectedPolynomials (Airbender.Compiler.HistoryErasureNative.MulDivUncached.native.protectedFields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.helperPlacement.memory)) := by
  have actual := fast_binding.trans (NumericHistoryErasureChecks.ofSource_eq Airbender.Compiler.HistoryErasureNative.MulDivUncached.native.historyCells
    Airbender.Compiler.SourceContractNative.MulDivUncached.native.originals Airbender.Compiler.SourceContractNative.MulDivUncached.native.clock Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.helperPlacement (Airbender.Compiler.HistoryErasureNative.MulDivUncached.native.protectedFields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.helperPlacement.memory)))
  simpa only [Airbender.Compiler.SourceContractNative.MulDivUncached.native.protectedPolynomials, Airbender.Compiler.SourceContractNative.MulDivUncached.native.clockPolynomials] using actual

end Airbender.Compiler.HistoryErasureChecks.MulDivUncached
