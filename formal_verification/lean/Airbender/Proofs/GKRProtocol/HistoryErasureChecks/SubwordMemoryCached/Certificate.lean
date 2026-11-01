import Airbender.Proofs.GKRProtocol.HistoryErasureChecks.SubwordMemoryCached.Bindings

namespace Airbender.Compiler.HistoryErasureChecks.SubwordMemoryCached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

private instance : NeZero babyBearModulus := ⟨by decide +kernel⟩

theorem checked : NumericHistoryErasureChecks.check babyBearModulus data = true := by decide +kernel

theorem originalChecked : Airbender.Compiler.HistoryErasureNative.SubwordMemoryCached.native.historyCells.Nodup ∧
  erasureCheck Airbender.Compiler.HistoryErasureNative.SubwordMemoryCached.native.historyCells Airbender.Compiler.SourceContractNative.SubwordMemoryCached.native.protectedPolynomials = true ∧
  (Airbender.Compiler.HistoryErasureNative.SubwordMemoryCached.native.protectedFields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.helperPlacement.memory)).all (fun polynomial => equal
    (substitute (erasurePolynomials Airbender.Compiler.HistoryErasureNative.SubwordMemoryCached.native.historyCells) polynomial) polynomial) = true :=
  NumericHistoryErasureChecks.check_sound data Airbender.Compiler.HistoryErasureNative.SubwordMemoryCached.native.historyCells
    Airbender.Compiler.SourceContractNative.SubwordMemoryCached.native.protectedPolynomials (Airbender.Compiler.HistoryErasureNative.SubwordMemoryCached.native.protectedFields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.helperPlacement.memory)) source_binding checked

end Airbender.Compiler.HistoryErasureChecks.SubwordMemoryCached
