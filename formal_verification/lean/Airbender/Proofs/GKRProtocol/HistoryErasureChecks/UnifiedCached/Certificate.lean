import Airbender.Proofs.GKRProtocol.HistoryErasureChecks.UnifiedCached.Bindings

namespace Airbender.Compiler.HistoryErasureChecks.UnifiedCached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

private instance : NeZero babyBearModulus := ⟨by decide +kernel⟩

theorem checked : NumericHistoryErasureChecks.check babyBearModulus data = true := by decide +kernel

theorem originalChecked : Airbender.Compiler.HistoryErasureNative.UnifiedCached.native.historyCells.Nodup ∧
  erasureCheck Airbender.Compiler.HistoryErasureNative.UnifiedCached.native.historyCells Airbender.Compiler.SourceContractNative.UnifiedCached.native.protectedPolynomials = true ∧
  (Airbender.Compiler.HistoryErasureNative.UnifiedCached.native.protectedFields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.helperPlacement.memory)).all (fun polynomial => equal
    (substitute (erasurePolynomials Airbender.Compiler.HistoryErasureNative.UnifiedCached.native.historyCells) polynomial) polynomial) = true :=
  NumericHistoryErasureChecks.check_sound data Airbender.Compiler.HistoryErasureNative.UnifiedCached.native.historyCells
    Airbender.Compiler.SourceContractNative.UnifiedCached.native.protectedPolynomials (Airbender.Compiler.HistoryErasureNative.UnifiedCached.native.protectedFields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.helperPlacement.memory)) source_binding checked

end Airbender.Compiler.HistoryErasureChecks.UnifiedCached
