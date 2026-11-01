import Airbender.Proofs.GKRProtocol.HistoryErasureChecks.MulDivUncached.Bindings

namespace Airbender.Compiler.HistoryErasureChecks.MulDivUncached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

private instance : NeZero babyBearModulus := ⟨by decide +kernel⟩

theorem checked : NumericHistoryErasureChecks.check babyBearModulus data = true := by decide +kernel

theorem originalChecked : Airbender.Compiler.HistoryErasureNative.MulDivUncached.native.historyCells.Nodup ∧
  erasureCheck Airbender.Compiler.HistoryErasureNative.MulDivUncached.native.historyCells Airbender.Compiler.SourceContractNative.MulDivUncached.native.protectedPolynomials = true ∧
  (Airbender.Compiler.HistoryErasureNative.MulDivUncached.native.protectedFields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.helperPlacement.memory)).all (fun polynomial => equal
    (substitute (erasurePolynomials Airbender.Compiler.HistoryErasureNative.MulDivUncached.native.historyCells) polynomial) polynomial) = true :=
  NumericHistoryErasureChecks.check_sound data Airbender.Compiler.HistoryErasureNative.MulDivUncached.native.historyCells
    Airbender.Compiler.SourceContractNative.MulDivUncached.native.protectedPolynomials (Airbender.Compiler.HistoryErasureNative.MulDivUncached.native.protectedFields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.helperPlacement.memory)) source_binding checked

end Airbender.Compiler.HistoryErasureChecks.MulDivUncached
