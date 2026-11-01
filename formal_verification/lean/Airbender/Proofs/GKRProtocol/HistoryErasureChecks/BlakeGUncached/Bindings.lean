import Airbender.Proofs.GKRProtocol.HistoryErasureChecks.BlakeGUncached.Data
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.HistoryErasureChecks.BlakeGUncached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

numeric_data_binding fast_binding : data = NumericHistoryErasureChecks.ofSource Airbender.Compiler.HistoryErasureNative.BlakeGUncached.native.historyCells Airbender.Compiler.SourceContractNative.BlakeGUncached.native.originals Airbender.Compiler.SourceContractNative.BlakeGUncached.native.clock Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.helperPlacement (Airbender.Compiler.HistoryErasureNative.BlakeGUncached.native.protectedFields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.helperPlacement.memory))

theorem source_binding : data = NumericHistoryErasureChecks.ofTyped Airbender.Compiler.HistoryErasureNative.BlakeGUncached.native.historyCells Airbender.Compiler.SourceContractNative.BlakeGUncached.native.protectedPolynomials (Airbender.Compiler.HistoryErasureNative.BlakeGUncached.native.protectedFields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.helperPlacement.memory)) := by
  have actual := fast_binding.trans (NumericHistoryErasureChecks.ofSource_eq Airbender.Compiler.HistoryErasureNative.BlakeGUncached.native.historyCells
    Airbender.Compiler.SourceContractNative.BlakeGUncached.native.originals Airbender.Compiler.SourceContractNative.BlakeGUncached.native.clock Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.helperPlacement (Airbender.Compiler.HistoryErasureNative.BlakeGUncached.native.protectedFields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.helperPlacement.memory)))
  simpa only [Airbender.Compiler.SourceContractNative.BlakeGUncached.native.protectedPolynomials, Airbender.Compiler.SourceContractNative.BlakeGUncached.native.clockPolynomials] using actual

end Airbender.Compiler.HistoryErasureChecks.BlakeGUncached
