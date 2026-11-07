import Airbender.Proofs.GKRProtocol.HistoryErasureChecks.WordMemoryCached.Data
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.HistoryErasureChecks.WordMemoryCached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

numeric_data_binding fast_binding : data = NumericHistoryErasureChecks.ofSource Airbender.Compiler.HistoryErasureNative.WordMemoryCached.native.historyCells Airbender.Compiler.SourceContractNative.WordMemoryCached.native.originals Airbender.Compiler.SourceContractNative.WordMemoryCached.native.clock Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.helperPlacement (Airbender.Compiler.HistoryErasureNative.WordMemoryCached.native.protectedFields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.helperPlacement.memory))

theorem source_binding : data = NumericHistoryErasureChecks.ofTyped Airbender.Compiler.HistoryErasureNative.WordMemoryCached.native.historyCells Airbender.Compiler.SourceContractNative.WordMemoryCached.native.protectedPolynomials (Airbender.Compiler.HistoryErasureNative.WordMemoryCached.native.protectedFields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.helperPlacement.memory)) := by
  have actual := fast_binding.trans (NumericHistoryErasureChecks.ofSource_eq Airbender.Compiler.HistoryErasureNative.WordMemoryCached.native.historyCells
    Airbender.Compiler.SourceContractNative.WordMemoryCached.native.originals Airbender.Compiler.SourceContractNative.WordMemoryCached.native.clock Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.helperPlacement (Airbender.Compiler.HistoryErasureNative.WordMemoryCached.native.protectedFields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.helperPlacement.memory)))
  simpa only [Airbender.Compiler.SourceContractNative.WordMemoryCached.native.protectedPolynomials, Airbender.Compiler.SourceContractNative.WordMemoryCached.native.clockPolynomials] using actual

end Airbender.Compiler.HistoryErasureChecks.WordMemoryCached
