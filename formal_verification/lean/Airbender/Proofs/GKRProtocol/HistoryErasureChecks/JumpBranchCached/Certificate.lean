import Airbender.Proofs.GKRProtocol.HistoryErasureChecks.JumpBranchCached.Bindings

namespace Airbender.Compiler.HistoryErasureChecks.JumpBranchCached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

private instance : NeZero babyBearModulus := ⟨by decide +kernel⟩

theorem checked : NumericHistoryErasureChecks.check babyBearModulus data = true := by decide +kernel

theorem originalChecked : Airbender.Compiler.HistoryErasureNative.JumpBranchCached.native.historyCells.Nodup ∧
  erasureCheck Airbender.Compiler.HistoryErasureNative.JumpBranchCached.native.historyCells Airbender.Compiler.SourceContractNative.JumpBranchCached.native.protectedPolynomials = true ∧
  (Airbender.Compiler.HistoryErasureNative.JumpBranchCached.native.protectedFields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.helperPlacement.memory)).all (fun polynomial => equal
    (substitute (erasurePolynomials Airbender.Compiler.HistoryErasureNative.JumpBranchCached.native.historyCells) polynomial) polynomial) = true :=
  NumericHistoryErasureChecks.check_sound data Airbender.Compiler.HistoryErasureNative.JumpBranchCached.native.historyCells
    Airbender.Compiler.SourceContractNative.JumpBranchCached.native.protectedPolynomials (Airbender.Compiler.HistoryErasureNative.JumpBranchCached.native.protectedFields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.helperPlacement.memory)) source_binding checked

end Airbender.Compiler.HistoryErasureChecks.JumpBranchCached
