import Airbender.Proofs.GKRProtocol.HistoryErasureChecks.AddSubCached.Bindings

namespace Airbender.Compiler.HistoryErasureChecks.AddSubCached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

private instance : NeZero babyBearModulus := ⟨by decide +kernel⟩

theorem checked : NumericHistoryErasureChecks.check babyBearModulus data = true := by decide +kernel

theorem originalChecked : Airbender.Compiler.HistoryErasureNative.AddSubCached.native.historyCells.Nodup ∧
  erasureCheck Airbender.Compiler.HistoryErasureNative.AddSubCached.native.historyCells Airbender.Compiler.SourceContractNative.AddSubCached.native.protectedPolynomials = true ∧
  (Airbender.Compiler.HistoryErasureNative.AddSubCached.native.protectedFields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.AddSubCached.native.helperPlacement.memory)).all (fun polynomial => equal
    (substitute (erasurePolynomials Airbender.Compiler.HistoryErasureNative.AddSubCached.native.historyCells) polynomial) polynomial) = true :=
  NumericHistoryErasureChecks.check_sound data Airbender.Compiler.HistoryErasureNative.AddSubCached.native.historyCells
    Airbender.Compiler.SourceContractNative.AddSubCached.native.protectedPolynomials (Airbender.Compiler.HistoryErasureNative.AddSubCached.native.protectedFields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.AddSubCached.native.helperPlacement.memory)) source_binding checked

end Airbender.Compiler.HistoryErasureChecks.AddSubCached
