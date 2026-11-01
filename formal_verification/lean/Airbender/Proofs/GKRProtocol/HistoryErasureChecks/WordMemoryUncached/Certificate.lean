import Airbender.Proofs.GKRProtocol.HistoryErasureChecks.WordMemoryUncached.Bindings

namespace Airbender.Compiler.HistoryErasureChecks.WordMemoryUncached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

private instance : NeZero babyBearModulus := ⟨by decide +kernel⟩

theorem checked : NumericHistoryErasureChecks.check babyBearModulus data = true := by decide +kernel

theorem originalChecked : Airbender.Compiler.HistoryErasureNative.WordMemoryUncached.native.historyCells.Nodup ∧
  erasureCheck Airbender.Compiler.HistoryErasureNative.WordMemoryUncached.native.historyCells Airbender.Compiler.SourceContractNative.WordMemoryUncached.native.protectedPolynomials = true ∧
  (Airbender.Compiler.HistoryErasureNative.WordMemoryUncached.native.protectedFields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.helperPlacement.memory)).all (fun polynomial => equal
    (substitute (erasurePolynomials Airbender.Compiler.HistoryErasureNative.WordMemoryUncached.native.historyCells) polynomial) polynomial) = true :=
  NumericHistoryErasureChecks.check_sound data Airbender.Compiler.HistoryErasureNative.WordMemoryUncached.native.historyCells
    Airbender.Compiler.SourceContractNative.WordMemoryUncached.native.protectedPolynomials (Airbender.Compiler.HistoryErasureNative.WordMemoryUncached.native.protectedFields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.helperPlacement.memory)) source_binding checked

end Airbender.Compiler.HistoryErasureChecks.WordMemoryUncached
