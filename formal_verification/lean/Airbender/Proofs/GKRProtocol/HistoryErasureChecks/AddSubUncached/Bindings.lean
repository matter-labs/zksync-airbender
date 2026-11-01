import Airbender.Proofs.GKRProtocol.HistoryErasureChecks.AddSubUncached.Data
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.HistoryErasureChecks.AddSubUncached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

numeric_data_binding fast_binding : data = NumericHistoryErasureChecks.ofSource Airbender.Compiler.HistoryErasureNative.AddSubUncached.native.historyCells Airbender.Compiler.SourceContractNative.AddSubUncached.native.originals Airbender.Compiler.SourceContractNative.AddSubUncached.native.clock Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.helperPlacement (Airbender.Compiler.HistoryErasureNative.AddSubUncached.native.protectedFields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.helperPlacement.memory))

theorem source_binding : data = NumericHistoryErasureChecks.ofTyped Airbender.Compiler.HistoryErasureNative.AddSubUncached.native.historyCells Airbender.Compiler.SourceContractNative.AddSubUncached.native.protectedPolynomials (Airbender.Compiler.HistoryErasureNative.AddSubUncached.native.protectedFields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.helperPlacement.memory)) := by
  have actual := fast_binding.trans (NumericHistoryErasureChecks.ofSource_eq Airbender.Compiler.HistoryErasureNative.AddSubUncached.native.historyCells
    Airbender.Compiler.SourceContractNative.AddSubUncached.native.originals Airbender.Compiler.SourceContractNative.AddSubUncached.native.clock Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.helperPlacement (Airbender.Compiler.HistoryErasureNative.AddSubUncached.native.protectedFields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.helperPlacement.memory)))
  simpa only [Airbender.Compiler.SourceContractNative.AddSubUncached.native.protectedPolynomials, Airbender.Compiler.SourceContractNative.AddSubUncached.native.clockPolynomials] using actual

end Airbender.Compiler.HistoryErasureChecks.AddSubUncached
