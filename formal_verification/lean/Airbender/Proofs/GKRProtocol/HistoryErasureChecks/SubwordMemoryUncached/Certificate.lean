import Airbender.Proofs.GKRProtocol.HistoryErasureChecks.SubwordMemoryUncached.Bindings

namespace Airbender.Compiler.HistoryErasureChecks.SubwordMemoryUncached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

private instance : NeZero babyBearModulus := ⟨by decide +kernel⟩

theorem checked : NumericHistoryErasureChecks.check babyBearModulus data = true := by decide +kernel

theorem originalChecked : Airbender.Compiler.HistoryErasureNative.SubwordMemoryUncached.native.historyCells.Nodup ∧
  erasureCheck Airbender.Compiler.HistoryErasureNative.SubwordMemoryUncached.native.historyCells Airbender.Compiler.SourceContractNative.SubwordMemoryUncached.native.protectedPolynomials = true ∧
  (Airbender.Compiler.HistoryErasureNative.SubwordMemoryUncached.native.protectedFields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.helperPlacement.memory)).all (fun polynomial => equal
    (substitute (erasurePolynomials Airbender.Compiler.HistoryErasureNative.SubwordMemoryUncached.native.historyCells) polynomial) polynomial) = true :=
  NumericHistoryErasureChecks.check_sound data Airbender.Compiler.HistoryErasureNative.SubwordMemoryUncached.native.historyCells
    Airbender.Compiler.SourceContractNative.SubwordMemoryUncached.native.protectedPolynomials (Airbender.Compiler.HistoryErasureNative.SubwordMemoryUncached.native.protectedFields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.helperPlacement.memory)) source_binding checked

end Airbender.Compiler.HistoryErasureChecks.SubwordMemoryUncached
