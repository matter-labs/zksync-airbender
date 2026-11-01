import Airbender.Proofs.GKRProtocol.HistoryErasureChecks.JumpBranchUncached.Bindings

namespace Airbender.Compiler.HistoryErasureChecks.JumpBranchUncached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

private instance : NeZero babyBearModulus := ⟨by decide +kernel⟩

theorem checked : NumericHistoryErasureChecks.check babyBearModulus data = true := by decide +kernel

theorem originalChecked : Airbender.Compiler.HistoryErasureNative.JumpBranchUncached.native.historyCells.Nodup ∧
  erasureCheck Airbender.Compiler.HistoryErasureNative.JumpBranchUncached.native.historyCells Airbender.Compiler.SourceContractNative.JumpBranchUncached.native.protectedPolynomials = true ∧
  (Airbender.Compiler.HistoryErasureNative.JumpBranchUncached.native.protectedFields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.helperPlacement.memory)).all (fun polynomial => equal
    (substitute (erasurePolynomials Airbender.Compiler.HistoryErasureNative.JumpBranchUncached.native.historyCells) polynomial) polynomial) = true :=
  NumericHistoryErasureChecks.check_sound data Airbender.Compiler.HistoryErasureNative.JumpBranchUncached.native.historyCells
    Airbender.Compiler.SourceContractNative.JumpBranchUncached.native.protectedPolynomials (Airbender.Compiler.HistoryErasureNative.JumpBranchUncached.native.protectedFields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.helperPlacement.memory)) source_binding checked

end Airbender.Compiler.HistoryErasureChecks.JumpBranchUncached
