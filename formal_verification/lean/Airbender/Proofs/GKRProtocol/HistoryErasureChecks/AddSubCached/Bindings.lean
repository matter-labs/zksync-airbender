import Airbender.Proofs.GKRProtocol.HistoryErasureChecks.AddSubCached.Data
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.HistoryErasureChecks.AddSubCached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

numeric_data_binding fast_binding : data = NumericHistoryErasureChecks.ofSource Airbender.Compiler.HistoryErasureNative.AddSubCached.native.historyCells Airbender.Compiler.SourceContractNative.AddSubCached.native.originals Airbender.Compiler.SourceContractNative.AddSubCached.native.clock Airbender.Compiler.FullArithmeticNative.AddSubCached.native.helperPlacement (Airbender.Compiler.HistoryErasureNative.AddSubCached.native.protectedFields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.AddSubCached.native.helperPlacement.memory))

theorem source_binding : data = NumericHistoryErasureChecks.ofTyped Airbender.Compiler.HistoryErasureNative.AddSubCached.native.historyCells Airbender.Compiler.SourceContractNative.AddSubCached.native.protectedPolynomials (Airbender.Compiler.HistoryErasureNative.AddSubCached.native.protectedFields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.AddSubCached.native.helperPlacement.memory)) := by
  have actual := fast_binding.trans (NumericHistoryErasureChecks.ofSource_eq Airbender.Compiler.HistoryErasureNative.AddSubCached.native.historyCells
    Airbender.Compiler.SourceContractNative.AddSubCached.native.originals Airbender.Compiler.SourceContractNative.AddSubCached.native.clock Airbender.Compiler.FullArithmeticNative.AddSubCached.native.helperPlacement (Airbender.Compiler.HistoryErasureNative.AddSubCached.native.protectedFields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.AddSubCached.native.helperPlacement.memory)))
  simpa only [Airbender.Compiler.SourceContractNative.AddSubCached.native.protectedPolynomials, Airbender.Compiler.SourceContractNative.AddSubCached.native.clockPolynomials] using actual

end Airbender.Compiler.HistoryErasureChecks.AddSubCached
