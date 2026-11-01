import Airbender.Proofs.GKRProtocol.HistoryErasureChecks.AddSubUncached.Bindings

namespace Airbender.Compiler.HistoryErasureChecks.AddSubUncached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

private instance : NeZero babyBearModulus := ⟨by decide +kernel⟩

theorem checked : NumericHistoryErasureChecks.check babyBearModulus data = true := by decide +kernel

theorem originalChecked : Airbender.Compiler.HistoryErasureNative.AddSubUncached.native.historyCells.Nodup ∧
  erasureCheck Airbender.Compiler.HistoryErasureNative.AddSubUncached.native.historyCells Airbender.Compiler.SourceContractNative.AddSubUncached.native.protectedPolynomials = true ∧
  (Airbender.Compiler.HistoryErasureNative.AddSubUncached.native.protectedFields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.helperPlacement.memory)).all (fun polynomial => equal
    (substitute (erasurePolynomials Airbender.Compiler.HistoryErasureNative.AddSubUncached.native.historyCells) polynomial) polynomial) = true :=
  NumericHistoryErasureChecks.check_sound data Airbender.Compiler.HistoryErasureNative.AddSubUncached.native.historyCells
    Airbender.Compiler.SourceContractNative.AddSubUncached.native.protectedPolynomials (Airbender.Compiler.HistoryErasureNative.AddSubUncached.native.protectedFields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.helperPlacement.memory)) source_binding checked

end Airbender.Compiler.HistoryErasureChecks.AddSubUncached
