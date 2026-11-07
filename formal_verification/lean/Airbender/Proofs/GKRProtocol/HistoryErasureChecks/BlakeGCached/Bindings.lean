import Airbender.Proofs.GKRProtocol.HistoryErasureChecks.BlakeGCached.Data
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.HistoryErasureChecks.BlakeGCached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

numeric_data_binding fast_binding : data = NumericHistoryErasureChecks.ofSource Airbender.Compiler.HistoryErasureNative.BlakeGCached.native.historyCells Airbender.Compiler.SourceContractNative.BlakeGCached.native.originals Airbender.Compiler.SourceContractNative.BlakeGCached.native.clock Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.helperPlacement (Airbender.Compiler.HistoryErasureNative.BlakeGCached.native.protectedFields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.helperPlacement.memory))

theorem source_binding : data = NumericHistoryErasureChecks.ofTyped Airbender.Compiler.HistoryErasureNative.BlakeGCached.native.historyCells Airbender.Compiler.SourceContractNative.BlakeGCached.native.protectedPolynomials (Airbender.Compiler.HistoryErasureNative.BlakeGCached.native.protectedFields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.helperPlacement.memory)) := by
  have actual := fast_binding.trans (NumericHistoryErasureChecks.ofSource_eq Airbender.Compiler.HistoryErasureNative.BlakeGCached.native.historyCells
    Airbender.Compiler.SourceContractNative.BlakeGCached.native.originals Airbender.Compiler.SourceContractNative.BlakeGCached.native.clock Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.helperPlacement (Airbender.Compiler.HistoryErasureNative.BlakeGCached.native.protectedFields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.helperPlacement.memory)))
  simpa only [Airbender.Compiler.SourceContractNative.BlakeGCached.native.protectedPolynomials, Airbender.Compiler.SourceContractNative.BlakeGCached.native.clockPolynomials] using actual

end Airbender.Compiler.HistoryErasureChecks.BlakeGCached
