import Airbender.Proofs.GKRProtocol.HistoryErasureChecks.BlakeGCached.Bindings

namespace Airbender.Compiler.HistoryErasureChecks.BlakeGCached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

private instance : NeZero babyBearModulus := ⟨by decide +kernel⟩

theorem checked : NumericHistoryErasureChecks.check babyBearModulus data = true := by decide +kernel

theorem originalChecked : Airbender.Compiler.HistoryErasureNative.BlakeGCached.native.historyCells.Nodup ∧
  erasureCheck Airbender.Compiler.HistoryErasureNative.BlakeGCached.native.historyCells Airbender.Compiler.SourceContractNative.BlakeGCached.native.protectedPolynomials = true ∧
  (Airbender.Compiler.HistoryErasureNative.BlakeGCached.native.protectedFields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.helperPlacement.memory)).all (fun polynomial => equal
    (substitute (erasurePolynomials Airbender.Compiler.HistoryErasureNative.BlakeGCached.native.historyCells) polynomial) polynomial) = true :=
  NumericHistoryErasureChecks.check_sound data Airbender.Compiler.HistoryErasureNative.BlakeGCached.native.historyCells
    Airbender.Compiler.SourceContractNative.BlakeGCached.native.protectedPolynomials (Airbender.Compiler.HistoryErasureNative.BlakeGCached.native.protectedFields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.helperPlacement.memory)) source_binding checked

end Airbender.Compiler.HistoryErasureChecks.BlakeGCached
