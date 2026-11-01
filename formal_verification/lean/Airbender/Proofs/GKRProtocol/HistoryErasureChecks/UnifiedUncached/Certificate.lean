import Airbender.Proofs.GKRProtocol.HistoryErasureChecks.UnifiedUncached.Bindings

namespace Airbender.Compiler.HistoryErasureChecks.UnifiedUncached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

private instance : NeZero babyBearModulus := ⟨by decide +kernel⟩

theorem checked : NumericHistoryErasureChecks.check babyBearModulus data = true := by decide +kernel

theorem originalChecked : Airbender.Compiler.HistoryErasureNative.UnifiedUncached.native.historyCells.Nodup ∧
  erasureCheck Airbender.Compiler.HistoryErasureNative.UnifiedUncached.native.historyCells Airbender.Compiler.SourceContractNative.UnifiedUncached.native.protectedPolynomials = true ∧
  (Airbender.Compiler.HistoryErasureNative.UnifiedUncached.native.protectedFields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.helperPlacement.memory)).all (fun polynomial => equal
    (substitute (erasurePolynomials Airbender.Compiler.HistoryErasureNative.UnifiedUncached.native.historyCells) polynomial) polynomial) = true :=
  NumericHistoryErasureChecks.check_sound data Airbender.Compiler.HistoryErasureNative.UnifiedUncached.native.historyCells
    Airbender.Compiler.SourceContractNative.UnifiedUncached.native.protectedPolynomials (Airbender.Compiler.HistoryErasureNative.UnifiedUncached.native.protectedFields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.helperPlacement.memory)) source_binding checked

end Airbender.Compiler.HistoryErasureChecks.UnifiedUncached
