import Airbender.Proofs.GKRProtocol.HistoryErasureChecks.KeccakCached.Bindings

namespace Airbender.Compiler.HistoryErasureChecks.KeccakCached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

private instance : NeZero babyBearModulus := ⟨by decide +kernel⟩

theorem checked : NumericHistoryErasureChecks.check babyBearModulus data = true := by decide +kernel

theorem originalChecked : Airbender.Compiler.HistoryErasureNative.KeccakCached.native.historyCells.Nodup ∧
  erasureCheck Airbender.Compiler.HistoryErasureNative.KeccakCached.native.historyCells Airbender.Compiler.SourceContractNative.KeccakCached.native.protectedPolynomials = true ∧
  (Airbender.Compiler.HistoryErasureNative.KeccakCached.native.protectedFields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.KeccakCached.native.helperPlacement.memory)).all (fun polynomial => equal
    (substitute (erasurePolynomials Airbender.Compiler.HistoryErasureNative.KeccakCached.native.historyCells) polynomial) polynomial) = true :=
  NumericHistoryErasureChecks.check_sound data Airbender.Compiler.HistoryErasureNative.KeccakCached.native.historyCells
    Airbender.Compiler.SourceContractNative.KeccakCached.native.protectedPolynomials (Airbender.Compiler.HistoryErasureNative.KeccakCached.native.protectedFields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.KeccakCached.native.helperPlacement.memory)) source_binding checked

end Airbender.Compiler.HistoryErasureChecks.KeccakCached
