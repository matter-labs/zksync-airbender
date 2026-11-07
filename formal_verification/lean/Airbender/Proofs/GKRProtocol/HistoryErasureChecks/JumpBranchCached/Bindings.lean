import Airbender.Proofs.GKRProtocol.HistoryErasureChecks.JumpBranchCached.Data
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.HistoryErasureChecks.JumpBranchCached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

numeric_data_binding fast_binding : data = NumericHistoryErasureChecks.ofSource Airbender.Compiler.HistoryErasureNative.JumpBranchCached.native.historyCells Airbender.Compiler.SourceContractNative.JumpBranchCached.native.originals Airbender.Compiler.SourceContractNative.JumpBranchCached.native.clock Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.helperPlacement (Airbender.Compiler.HistoryErasureNative.JumpBranchCached.native.protectedFields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.helperPlacement.memory))

theorem source_binding : data = NumericHistoryErasureChecks.ofTyped Airbender.Compiler.HistoryErasureNative.JumpBranchCached.native.historyCells Airbender.Compiler.SourceContractNative.JumpBranchCached.native.protectedPolynomials (Airbender.Compiler.HistoryErasureNative.JumpBranchCached.native.protectedFields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.helperPlacement.memory)) := by
  have actual := fast_binding.trans (NumericHistoryErasureChecks.ofSource_eq Airbender.Compiler.HistoryErasureNative.JumpBranchCached.native.historyCells
    Airbender.Compiler.SourceContractNative.JumpBranchCached.native.originals Airbender.Compiler.SourceContractNative.JumpBranchCached.native.clock Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.helperPlacement (Airbender.Compiler.HistoryErasureNative.JumpBranchCached.native.protectedFields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.helperPlacement.memory)))
  simpa only [Airbender.Compiler.SourceContractNative.JumpBranchCached.native.protectedPolynomials, Airbender.Compiler.SourceContractNative.JumpBranchCached.native.clockPolynomials] using actual

end Airbender.Compiler.HistoryErasureChecks.JumpBranchCached
