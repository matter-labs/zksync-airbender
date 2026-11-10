import Airbender.Proofs.GKRProtocol.HistoryErasureChecks.BigintCached.Data
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.HistoryErasureChecks.BigintCached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

numeric_data_binding fast_binding : data = NumericHistoryErasureChecks.ofSource Airbender.Compiler.HistoryErasureNative.BigintCached.native.historyCells Airbender.Compiler.SourceContractNative.BigintCached.native.originals Airbender.Compiler.SourceContractNative.BigintCached.native.clock Airbender.Compiler.FullArithmeticNative.BigintCached.native.helperPlacement (Airbender.Compiler.HistoryErasureNative.BigintCached.native.protectedFields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.BigintCached.native.helperPlacement.memory))

theorem source_binding : data = NumericHistoryErasureChecks.ofTyped Airbender.Compiler.HistoryErasureNative.BigintCached.native.historyCells Airbender.Compiler.SourceContractNative.BigintCached.native.protectedPolynomials (Airbender.Compiler.HistoryErasureNative.BigintCached.native.protectedFields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.BigintCached.native.helperPlacement.memory)) := by
  have actual := fast_binding.trans (NumericHistoryErasureChecks.ofSource_eq Airbender.Compiler.HistoryErasureNative.BigintCached.native.historyCells
    Airbender.Compiler.SourceContractNative.BigintCached.native.originals Airbender.Compiler.SourceContractNative.BigintCached.native.clock Airbender.Compiler.FullArithmeticNative.BigintCached.native.helperPlacement (Airbender.Compiler.HistoryErasureNative.BigintCached.native.protectedFields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.BigintCached.native.helperPlacement.memory)))
  simpa only [Airbender.Compiler.SourceContractNative.BigintCached.native.protectedPolynomials, Airbender.Compiler.SourceContractNative.BigintCached.native.clockPolynomials] using actual

end Airbender.Compiler.HistoryErasureChecks.BigintCached
