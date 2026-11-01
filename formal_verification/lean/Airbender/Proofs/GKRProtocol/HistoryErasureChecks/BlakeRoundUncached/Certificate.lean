import Airbender.Proofs.GKRProtocol.HistoryErasureChecks.BlakeRoundUncached.Bindings

namespace Airbender.Compiler.HistoryErasureChecks.BlakeRoundUncached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

private instance : NeZero babyBearModulus := ⟨by decide +kernel⟩

theorem checked : NumericHistoryErasureChecks.check babyBearModulus data = true := by decide +kernel

theorem originalChecked : Airbender.Compiler.HistoryErasureNative.BlakeRoundUncached.native.historyCells.Nodup ∧
  erasureCheck Airbender.Compiler.HistoryErasureNative.BlakeRoundUncached.native.historyCells Airbender.Compiler.SourceContractNative.BlakeRoundUncached.native.protectedPolynomials = true ∧
  (Airbender.Compiler.HistoryErasureNative.BlakeRoundUncached.native.protectedFields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.helperPlacement.memory)).all (fun polynomial => equal
    (substitute (erasurePolynomials Airbender.Compiler.HistoryErasureNative.BlakeRoundUncached.native.historyCells) polynomial) polynomial) = true :=
  NumericHistoryErasureChecks.check_sound data Airbender.Compiler.HistoryErasureNative.BlakeRoundUncached.native.historyCells
    Airbender.Compiler.SourceContractNative.BlakeRoundUncached.native.protectedPolynomials (Airbender.Compiler.HistoryErasureNative.BlakeRoundUncached.native.protectedFields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.helperPlacement.memory)) source_binding checked

end Airbender.Compiler.HistoryErasureChecks.BlakeRoundUncached
