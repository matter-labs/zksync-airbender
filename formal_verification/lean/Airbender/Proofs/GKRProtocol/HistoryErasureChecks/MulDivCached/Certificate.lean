import Airbender.Proofs.GKRProtocol.HistoryErasureChecks.MulDivCached.Bindings

namespace Airbender.Compiler.HistoryErasureChecks.MulDivCached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

private instance : NeZero babyBearModulus := ⟨by decide +kernel⟩

theorem checked : NumericHistoryErasureChecks.check babyBearModulus data = true := by decide +kernel

theorem originalChecked : Airbender.Compiler.HistoryErasureNative.MulDivCached.native.historyCells.Nodup ∧
  erasureCheck Airbender.Compiler.HistoryErasureNative.MulDivCached.native.historyCells Airbender.Compiler.SourceContractNative.MulDivCached.native.protectedPolynomials = true ∧
  (Airbender.Compiler.HistoryErasureNative.MulDivCached.native.protectedFields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.MulDivCached.native.helperPlacement.memory)).all (fun polynomial => equal
    (substitute (erasurePolynomials Airbender.Compiler.HistoryErasureNative.MulDivCached.native.historyCells) polynomial) polynomial) = true :=
  NumericHistoryErasureChecks.check_sound data Airbender.Compiler.HistoryErasureNative.MulDivCached.native.historyCells
    Airbender.Compiler.SourceContractNative.MulDivCached.native.protectedPolynomials (Airbender.Compiler.HistoryErasureNative.MulDivCached.native.protectedFields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.MulDivCached.native.helperPlacement.memory)) source_binding checked

end Airbender.Compiler.HistoryErasureChecks.MulDivCached
