import Airbender.Proofs.GKRProtocol.HistoryErasureChecks.UnifiedUncached.Data
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.HistoryErasureChecks.UnifiedUncached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

numeric_data_binding fast_binding : data = NumericHistoryErasureChecks.ofSource Airbender.Compiler.HistoryErasureNative.UnifiedUncached.native.historyCells Airbender.Compiler.SourceContractNative.UnifiedUncached.native.originals Airbender.Compiler.SourceContractNative.UnifiedUncached.native.clock Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.helperPlacement (Airbender.Compiler.HistoryErasureNative.UnifiedUncached.native.protectedFields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.helperPlacement.memory))

theorem source_binding : data = NumericHistoryErasureChecks.ofTyped Airbender.Compiler.HistoryErasureNative.UnifiedUncached.native.historyCells Airbender.Compiler.SourceContractNative.UnifiedUncached.native.protectedPolynomials (Airbender.Compiler.HistoryErasureNative.UnifiedUncached.native.protectedFields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.helperPlacement.memory)) := by
  have actual := fast_binding.trans (NumericHistoryErasureChecks.ofSource_eq Airbender.Compiler.HistoryErasureNative.UnifiedUncached.native.historyCells
    Airbender.Compiler.SourceContractNative.UnifiedUncached.native.originals Airbender.Compiler.SourceContractNative.UnifiedUncached.native.clock Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.helperPlacement (Airbender.Compiler.HistoryErasureNative.UnifiedUncached.native.protectedFields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.helperPlacement.memory)))
  simpa only [Airbender.Compiler.SourceContractNative.UnifiedUncached.native.protectedPolynomials, Airbender.Compiler.SourceContractNative.UnifiedUncached.native.clockPolynomials] using actual

end Airbender.Compiler.HistoryErasureChecks.UnifiedUncached
