import Airbender.Proofs.GKRProtocol.HistoryErasureChecks.BigintCached.Bindings

namespace Airbender.Compiler.HistoryErasureChecks.BigintCached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

private instance : NeZero babyBearModulus := ⟨by decide +kernel⟩

theorem checked : NumericHistoryErasureChecks.check babyBearModulus data = true := by decide +kernel

theorem originalChecked : Airbender.Compiler.HistoryErasureNative.BigintCached.native.historyCells.Nodup ∧
  erasureCheck Airbender.Compiler.HistoryErasureNative.BigintCached.native.historyCells Airbender.Compiler.SourceContractNative.BigintCached.native.protectedPolynomials = true ∧
  (Airbender.Compiler.HistoryErasureNative.BigintCached.native.protectedFields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.BigintCached.native.helperPlacement.memory)).all (fun polynomial => equal
    (substitute (erasurePolynomials Airbender.Compiler.HistoryErasureNative.BigintCached.native.historyCells) polynomial) polynomial) = true :=
  NumericHistoryErasureChecks.check_sound data Airbender.Compiler.HistoryErasureNative.BigintCached.native.historyCells
    Airbender.Compiler.SourceContractNative.BigintCached.native.protectedPolynomials (Airbender.Compiler.HistoryErasureNative.BigintCached.native.protectedFields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.BigintCached.native.helperPlacement.memory)) source_binding checked

end Airbender.Compiler.HistoryErasureChecks.BigintCached
