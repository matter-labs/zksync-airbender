import Airbender.Proofs.GKRProtocol.HistoryErasureChecks.BlakeRoundUncached.Data
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.HistoryErasureChecks.BlakeRoundUncached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

numeric_data_binding fast_binding : data = NumericHistoryErasureChecks.ofSource Airbender.Compiler.HistoryErasureNative.BlakeRoundUncached.native.historyCells Airbender.Compiler.SourceContractNative.BlakeRoundUncached.native.originals Airbender.Compiler.SourceContractNative.BlakeRoundUncached.native.clock Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.helperPlacement (Airbender.Compiler.HistoryErasureNative.BlakeRoundUncached.native.protectedFields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.helperPlacement.memory))

theorem source_binding : data = NumericHistoryErasureChecks.ofTyped Airbender.Compiler.HistoryErasureNative.BlakeRoundUncached.native.historyCells Airbender.Compiler.SourceContractNative.BlakeRoundUncached.native.protectedPolynomials (Airbender.Compiler.HistoryErasureNative.BlakeRoundUncached.native.protectedFields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.helperPlacement.memory)) := by
  have actual := fast_binding.trans (NumericHistoryErasureChecks.ofSource_eq Airbender.Compiler.HistoryErasureNative.BlakeRoundUncached.native.historyCells
    Airbender.Compiler.SourceContractNative.BlakeRoundUncached.native.originals Airbender.Compiler.SourceContractNative.BlakeRoundUncached.native.clock Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.helperPlacement (Airbender.Compiler.HistoryErasureNative.BlakeRoundUncached.native.protectedFields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.helperPlacement.memory)))
  simpa only [Airbender.Compiler.SourceContractNative.BlakeRoundUncached.native.protectedPolynomials, Airbender.Compiler.SourceContractNative.BlakeRoundUncached.native.clockPolynomials] using actual

end Airbender.Compiler.HistoryErasureChecks.BlakeRoundUncached
