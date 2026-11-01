import Airbender.Proofs.GKRProtocol.HistoryErasureChecks.SubwordMemoryUncached.Data
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.HistoryErasureChecks.SubwordMemoryUncached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

numeric_data_binding fast_binding : data = NumericHistoryErasureChecks.ofSource Airbender.Compiler.HistoryErasureNative.SubwordMemoryUncached.native.historyCells Airbender.Compiler.SourceContractNative.SubwordMemoryUncached.native.originals Airbender.Compiler.SourceContractNative.SubwordMemoryUncached.native.clock Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.helperPlacement (Airbender.Compiler.HistoryErasureNative.SubwordMemoryUncached.native.protectedFields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.helperPlacement.memory))

theorem source_binding : data = NumericHistoryErasureChecks.ofTyped Airbender.Compiler.HistoryErasureNative.SubwordMemoryUncached.native.historyCells Airbender.Compiler.SourceContractNative.SubwordMemoryUncached.native.protectedPolynomials (Airbender.Compiler.HistoryErasureNative.SubwordMemoryUncached.native.protectedFields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.helperPlacement.memory)) := by
  have actual := fast_binding.trans (NumericHistoryErasureChecks.ofSource_eq Airbender.Compiler.HistoryErasureNative.SubwordMemoryUncached.native.historyCells
    Airbender.Compiler.SourceContractNative.SubwordMemoryUncached.native.originals Airbender.Compiler.SourceContractNative.SubwordMemoryUncached.native.clock Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.helperPlacement (Airbender.Compiler.HistoryErasureNative.SubwordMemoryUncached.native.protectedFields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.helperPlacement.memory)))
  simpa only [Airbender.Compiler.SourceContractNative.SubwordMemoryUncached.native.protectedPolynomials, Airbender.Compiler.SourceContractNative.SubwordMemoryUncached.native.clockPolynomials] using actual

end Airbender.Compiler.HistoryErasureChecks.SubwordMemoryUncached
