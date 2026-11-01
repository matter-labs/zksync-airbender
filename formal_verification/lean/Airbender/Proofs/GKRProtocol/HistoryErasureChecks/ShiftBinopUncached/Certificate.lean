import Airbender.Proofs.GKRProtocol.HistoryErasureChecks.ShiftBinopUncached.Bindings

namespace Airbender.Compiler.HistoryErasureChecks.ShiftBinopUncached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

private instance : NeZero babyBearModulus := ⟨by decide +kernel⟩

theorem checked : NumericHistoryErasureChecks.check babyBearModulus data = true := by decide +kernel

theorem originalChecked : Airbender.Compiler.HistoryErasureNative.ShiftBinopUncached.native.historyCells.Nodup ∧
  erasureCheck Airbender.Compiler.HistoryErasureNative.ShiftBinopUncached.native.historyCells Airbender.Compiler.SourceContractNative.ShiftBinopUncached.native.protectedPolynomials = true ∧
  (Airbender.Compiler.HistoryErasureNative.ShiftBinopUncached.native.protectedFields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.helperPlacement.memory)).all (fun polynomial => equal
    (substitute (erasurePolynomials Airbender.Compiler.HistoryErasureNative.ShiftBinopUncached.native.historyCells) polynomial) polynomial) = true :=
  NumericHistoryErasureChecks.check_sound data Airbender.Compiler.HistoryErasureNative.ShiftBinopUncached.native.historyCells
    Airbender.Compiler.SourceContractNative.ShiftBinopUncached.native.protectedPolynomials (Airbender.Compiler.HistoryErasureNative.ShiftBinopUncached.native.protectedFields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.helperPlacement.memory)) source_binding checked

end Airbender.Compiler.HistoryErasureChecks.ShiftBinopUncached
