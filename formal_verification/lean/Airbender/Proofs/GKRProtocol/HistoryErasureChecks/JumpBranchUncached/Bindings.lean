import Airbender.Proofs.GKRProtocol.HistoryErasureChecks.JumpBranchUncached.Data
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.HistoryErasureChecks.JumpBranchUncached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

numeric_data_binding fast_binding : data = NumericHistoryErasureChecks.ofSource Airbender.Compiler.HistoryErasureNative.JumpBranchUncached.native.historyCells Airbender.Compiler.SourceContractNative.JumpBranchUncached.native.originals Airbender.Compiler.SourceContractNative.JumpBranchUncached.native.clock Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.helperPlacement (Airbender.Compiler.HistoryErasureNative.JumpBranchUncached.native.protectedFields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.helperPlacement.memory))

theorem source_binding : data = NumericHistoryErasureChecks.ofTyped Airbender.Compiler.HistoryErasureNative.JumpBranchUncached.native.historyCells Airbender.Compiler.SourceContractNative.JumpBranchUncached.native.protectedPolynomials (Airbender.Compiler.HistoryErasureNative.JumpBranchUncached.native.protectedFields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.helperPlacement.memory)) := by
  have actual := fast_binding.trans (NumericHistoryErasureChecks.ofSource_eq Airbender.Compiler.HistoryErasureNative.JumpBranchUncached.native.historyCells
    Airbender.Compiler.SourceContractNative.JumpBranchUncached.native.originals Airbender.Compiler.SourceContractNative.JumpBranchUncached.native.clock Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.helperPlacement (Airbender.Compiler.HistoryErasureNative.JumpBranchUncached.native.protectedFields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.helperPlacement.memory)))
  simpa only [Airbender.Compiler.SourceContractNative.JumpBranchUncached.native.protectedPolynomials, Airbender.Compiler.SourceContractNative.JumpBranchUncached.native.clockPolynomials] using actual

end Airbender.Compiler.HistoryErasureChecks.JumpBranchUncached
