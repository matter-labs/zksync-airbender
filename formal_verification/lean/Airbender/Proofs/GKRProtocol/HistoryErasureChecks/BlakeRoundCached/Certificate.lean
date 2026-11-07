import Airbender.Proofs.GKRProtocol.HistoryErasureChecks.BlakeRoundCached.Bindings

namespace Airbender.Compiler.HistoryErasureChecks.BlakeRoundCached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

private instance : NeZero babyBearModulus := ⟨by decide +kernel⟩

theorem checked : NumericHistoryErasureChecks.check babyBearModulus data = true := by decide +kernel

theorem originalChecked : Airbender.Compiler.HistoryErasureNative.BlakeRoundCached.native.historyCells.Nodup ∧
  erasureCheck Airbender.Compiler.HistoryErasureNative.BlakeRoundCached.native.historyCells Airbender.Compiler.SourceContractNative.BlakeRoundCached.native.protectedPolynomials = true ∧
  (Airbender.Compiler.HistoryErasureNative.BlakeRoundCached.native.protectedFields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.helperPlacement.memory)).all (fun polynomial => equal
    (substitute (erasurePolynomials Airbender.Compiler.HistoryErasureNative.BlakeRoundCached.native.historyCells) polynomial) polynomial) = true :=
  NumericHistoryErasureChecks.check_sound data Airbender.Compiler.HistoryErasureNative.BlakeRoundCached.native.historyCells
    Airbender.Compiler.SourceContractNative.BlakeRoundCached.native.protectedPolynomials (Airbender.Compiler.HistoryErasureNative.BlakeRoundCached.native.protectedFields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.helperPlacement.memory)) source_binding checked

end Airbender.Compiler.HistoryErasureChecks.BlakeRoundCached
