import Airbender.Proofs.GKRProtocol.HistoryErasureChecks.MulDivCached.Data
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.HistoryErasureChecks.MulDivCached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

numeric_data_binding fast_binding : data = NumericHistoryErasureChecks.ofSource Airbender.Compiler.HistoryErasureNative.MulDivCached.native.historyCells Airbender.Compiler.SourceContractNative.MulDivCached.native.originals Airbender.Compiler.SourceContractNative.MulDivCached.native.clock Airbender.Compiler.FullArithmeticNative.MulDivCached.native.helperPlacement (Airbender.Compiler.HistoryErasureNative.MulDivCached.native.protectedFields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.MulDivCached.native.helperPlacement.memory))

theorem source_binding : data = NumericHistoryErasureChecks.ofTyped Airbender.Compiler.HistoryErasureNative.MulDivCached.native.historyCells Airbender.Compiler.SourceContractNative.MulDivCached.native.protectedPolynomials (Airbender.Compiler.HistoryErasureNative.MulDivCached.native.protectedFields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.MulDivCached.native.helperPlacement.memory)) := by
  have actual := fast_binding.trans (NumericHistoryErasureChecks.ofSource_eq Airbender.Compiler.HistoryErasureNative.MulDivCached.native.historyCells
    Airbender.Compiler.SourceContractNative.MulDivCached.native.originals Airbender.Compiler.SourceContractNative.MulDivCached.native.clock Airbender.Compiler.FullArithmeticNative.MulDivCached.native.helperPlacement (Airbender.Compiler.HistoryErasureNative.MulDivCached.native.protectedFields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.MulDivCached.native.helperPlacement.memory)))
  simpa only [Airbender.Compiler.SourceContractNative.MulDivCached.native.protectedPolynomials, Airbender.Compiler.SourceContractNative.MulDivCached.native.clockPolynomials] using actual

end Airbender.Compiler.HistoryErasureChecks.MulDivCached
