import Airbender.Proofs.GKRProtocol.HistoryErasureChecks.BlakeGUncached.Bindings

namespace Airbender.Compiler.HistoryErasureChecks.BlakeGUncached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

private instance : NeZero babyBearModulus := ⟨by decide +kernel⟩

theorem checked : NumericHistoryErasureChecks.check babyBearModulus data = true := by decide +kernel

theorem originalChecked : Airbender.Compiler.HistoryErasureNative.BlakeGUncached.native.historyCells.Nodup ∧
  erasureCheck Airbender.Compiler.HistoryErasureNative.BlakeGUncached.native.historyCells Airbender.Compiler.SourceContractNative.BlakeGUncached.native.protectedPolynomials = true ∧
  (Airbender.Compiler.HistoryErasureNative.BlakeGUncached.native.protectedFields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.helperPlacement.memory)).all (fun polynomial => equal
    (substitute (erasurePolynomials Airbender.Compiler.HistoryErasureNative.BlakeGUncached.native.historyCells) polynomial) polynomial) = true :=
  NumericHistoryErasureChecks.check_sound data Airbender.Compiler.HistoryErasureNative.BlakeGUncached.native.historyCells
    Airbender.Compiler.SourceContractNative.BlakeGUncached.native.protectedPolynomials (Airbender.Compiler.HistoryErasureNative.BlakeGUncached.native.protectedFields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.helperPlacement.memory)) source_binding checked

end Airbender.Compiler.HistoryErasureChecks.BlakeGUncached
