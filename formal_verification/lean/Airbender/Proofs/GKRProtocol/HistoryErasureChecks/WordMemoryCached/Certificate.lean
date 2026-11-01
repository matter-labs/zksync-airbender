import Airbender.Proofs.GKRProtocol.HistoryErasureChecks.WordMemoryCached.Bindings

namespace Airbender.Compiler.HistoryErasureChecks.WordMemoryCached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

private instance : NeZero babyBearModulus := ⟨by decide +kernel⟩

theorem checked : NumericHistoryErasureChecks.check babyBearModulus data = true := by decide +kernel

theorem originalChecked : Airbender.Compiler.HistoryErasureNative.WordMemoryCached.native.historyCells.Nodup ∧
  erasureCheck Airbender.Compiler.HistoryErasureNative.WordMemoryCached.native.historyCells Airbender.Compiler.SourceContractNative.WordMemoryCached.native.protectedPolynomials = true ∧
  (Airbender.Compiler.HistoryErasureNative.WordMemoryCached.native.protectedFields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.helperPlacement.memory)).all (fun polynomial => equal
    (substitute (erasurePolynomials Airbender.Compiler.HistoryErasureNative.WordMemoryCached.native.historyCells) polynomial) polynomial) = true :=
  NumericHistoryErasureChecks.check_sound data Airbender.Compiler.HistoryErasureNative.WordMemoryCached.native.historyCells
    Airbender.Compiler.SourceContractNative.WordMemoryCached.native.protectedPolynomials (Airbender.Compiler.HistoryErasureNative.WordMemoryCached.native.protectedFields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.helperPlacement.memory)) source_binding checked

end Airbender.Compiler.HistoryErasureChecks.WordMemoryCached
