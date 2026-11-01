import Airbender.Proofs.GKRProtocol.HistoryErasureChecks.SubwordMemoryCached.Data
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.HistoryErasureChecks.SubwordMemoryCached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

numeric_data_binding fast_binding : data = NumericHistoryErasureChecks.ofSource Airbender.Compiler.HistoryErasureNative.SubwordMemoryCached.native.historyCells Airbender.Compiler.SourceContractNative.SubwordMemoryCached.native.originals Airbender.Compiler.SourceContractNative.SubwordMemoryCached.native.clock Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.helperPlacement (Airbender.Compiler.HistoryErasureNative.SubwordMemoryCached.native.protectedFields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.helperPlacement.memory))

theorem source_binding : data = NumericHistoryErasureChecks.ofTyped Airbender.Compiler.HistoryErasureNative.SubwordMemoryCached.native.historyCells Airbender.Compiler.SourceContractNative.SubwordMemoryCached.native.protectedPolynomials (Airbender.Compiler.HistoryErasureNative.SubwordMemoryCached.native.protectedFields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.helperPlacement.memory)) := by
  have actual := fast_binding.trans (NumericHistoryErasureChecks.ofSource_eq Airbender.Compiler.HistoryErasureNative.SubwordMemoryCached.native.historyCells
    Airbender.Compiler.SourceContractNative.SubwordMemoryCached.native.originals Airbender.Compiler.SourceContractNative.SubwordMemoryCached.native.clock Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.helperPlacement (Airbender.Compiler.HistoryErasureNative.SubwordMemoryCached.native.protectedFields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.helperPlacement.memory)))
  simpa only [Airbender.Compiler.SourceContractNative.SubwordMemoryCached.native.protectedPolynomials, Airbender.Compiler.SourceContractNative.SubwordMemoryCached.native.clockPolynomials] using actual

end Airbender.Compiler.HistoryErasureChecks.SubwordMemoryCached
