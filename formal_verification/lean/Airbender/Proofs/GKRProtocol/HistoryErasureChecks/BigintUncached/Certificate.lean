import Airbender.Proofs.GKRProtocol.HistoryErasureChecks.BigintUncached.Bindings

namespace Airbender.Compiler.HistoryErasureChecks.BigintUncached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

private instance : NeZero babyBearModulus := ⟨by decide +kernel⟩

theorem checked : NumericHistoryErasureChecks.check babyBearModulus data = true := by decide +kernel

theorem originalChecked : Airbender.Compiler.HistoryErasureNative.BigintUncached.native.historyCells.Nodup ∧
  erasureCheck Airbender.Compiler.HistoryErasureNative.BigintUncached.native.historyCells Airbender.Compiler.SourceContractNative.BigintUncached.native.protectedPolynomials = true ∧
  (Airbender.Compiler.HistoryErasureNative.BigintUncached.native.protectedFields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.BigintUncached.native.helperPlacement.memory)).all (fun polynomial => equal
    (substitute (erasurePolynomials Airbender.Compiler.HistoryErasureNative.BigintUncached.native.historyCells) polynomial) polynomial) = true :=
  NumericHistoryErasureChecks.check_sound data Airbender.Compiler.HistoryErasureNative.BigintUncached.native.historyCells
    Airbender.Compiler.SourceContractNative.BigintUncached.native.protectedPolynomials (Airbender.Compiler.HistoryErasureNative.BigintUncached.native.protectedFields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.BigintUncached.native.helperPlacement.memory)) source_binding checked

end Airbender.Compiler.HistoryErasureChecks.BigintUncached
