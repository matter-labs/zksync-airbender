import Airbender.Proofs.GKRProtocol.HistoryErasureChecks.ShiftBinopCached.Bindings

namespace Airbender.Compiler.HistoryErasureChecks.ShiftBinopCached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

private instance : NeZero babyBearModulus := ⟨by decide +kernel⟩

theorem checked : NumericHistoryErasureChecks.check babyBearModulus data = true := by decide +kernel

theorem originalChecked : Airbender.Compiler.HistoryErasureNative.ShiftBinopCached.native.historyCells.Nodup ∧
  erasureCheck Airbender.Compiler.HistoryErasureNative.ShiftBinopCached.native.historyCells Airbender.Compiler.SourceContractNative.ShiftBinopCached.native.protectedPolynomials = true ∧
  (Airbender.Compiler.HistoryErasureNative.ShiftBinopCached.native.protectedFields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.helperPlacement.memory)).all (fun polynomial => equal
    (substitute (erasurePolynomials Airbender.Compiler.HistoryErasureNative.ShiftBinopCached.native.historyCells) polynomial) polynomial) = true :=
  NumericHistoryErasureChecks.check_sound data Airbender.Compiler.HistoryErasureNative.ShiftBinopCached.native.historyCells
    Airbender.Compiler.SourceContractNative.ShiftBinopCached.native.protectedPolynomials (Airbender.Compiler.HistoryErasureNative.ShiftBinopCached.native.protectedFields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.helperPlacement.memory)) source_binding checked

end Airbender.Compiler.HistoryErasureChecks.ShiftBinopCached
