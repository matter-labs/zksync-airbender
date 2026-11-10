import Airbender.Proofs.GKRProtocol.HistoryErasureChecks.BlakeRoundCached.Data
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.HistoryErasureChecks.BlakeRoundCached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

numeric_data_binding fast_binding : data = NumericHistoryErasureChecks.ofSource Airbender.Compiler.HistoryErasureNative.BlakeRoundCached.native.historyCells Airbender.Compiler.SourceContractNative.BlakeRoundCached.native.originals Airbender.Compiler.SourceContractNative.BlakeRoundCached.native.clock Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.helperPlacement (Airbender.Compiler.HistoryErasureNative.BlakeRoundCached.native.protectedFields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.helperPlacement.memory))

theorem source_binding : data = NumericHistoryErasureChecks.ofTyped Airbender.Compiler.HistoryErasureNative.BlakeRoundCached.native.historyCells Airbender.Compiler.SourceContractNative.BlakeRoundCached.native.protectedPolynomials (Airbender.Compiler.HistoryErasureNative.BlakeRoundCached.native.protectedFields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.helperPlacement.memory)) := by
  have actual := fast_binding.trans (NumericHistoryErasureChecks.ofSource_eq Airbender.Compiler.HistoryErasureNative.BlakeRoundCached.native.historyCells
    Airbender.Compiler.SourceContractNative.BlakeRoundCached.native.originals Airbender.Compiler.SourceContractNative.BlakeRoundCached.native.clock Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.helperPlacement (Airbender.Compiler.HistoryErasureNative.BlakeRoundCached.native.protectedFields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.helperPlacement.memory)))
  simpa only [Airbender.Compiler.SourceContractNative.BlakeRoundCached.native.protectedPolynomials, Airbender.Compiler.SourceContractNative.BlakeRoundCached.native.clockPolynomials] using actual

end Airbender.Compiler.HistoryErasureChecks.BlakeRoundCached
