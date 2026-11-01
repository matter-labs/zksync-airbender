import Airbender.Proofs.GKRProtocol.HistoryErasureChecks.UnifiedCached.Data
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.HistoryErasureChecks.UnifiedCached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

numeric_data_binding fast_binding : data = NumericHistoryErasureChecks.ofSource Airbender.Compiler.HistoryErasureNative.UnifiedCached.native.historyCells Airbender.Compiler.SourceContractNative.UnifiedCached.native.originals Airbender.Compiler.SourceContractNative.UnifiedCached.native.clock Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.helperPlacement (Airbender.Compiler.HistoryErasureNative.UnifiedCached.native.protectedFields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.helperPlacement.memory))

theorem source_binding : data = NumericHistoryErasureChecks.ofTyped Airbender.Compiler.HistoryErasureNative.UnifiedCached.native.historyCells Airbender.Compiler.SourceContractNative.UnifiedCached.native.protectedPolynomials (Airbender.Compiler.HistoryErasureNative.UnifiedCached.native.protectedFields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.helperPlacement.memory)) := by
  have actual := fast_binding.trans (NumericHistoryErasureChecks.ofSource_eq Airbender.Compiler.HistoryErasureNative.UnifiedCached.native.historyCells
    Airbender.Compiler.SourceContractNative.UnifiedCached.native.originals Airbender.Compiler.SourceContractNative.UnifiedCached.native.clock Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.helperPlacement (Airbender.Compiler.HistoryErasureNative.UnifiedCached.native.protectedFields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.helperPlacement.memory)))
  simpa only [Airbender.Compiler.SourceContractNative.UnifiedCached.native.protectedPolynomials, Airbender.Compiler.SourceContractNative.UnifiedCached.native.clockPolynomials] using actual

end Airbender.Compiler.HistoryErasureChecks.UnifiedCached
