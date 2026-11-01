import Airbender.Proofs.GKRProtocol.CleanIdealNative.BlakeRoundUncachedBindings

namespace Airbender.Compiler.CleanIdealNative.BlakeRoundUncached
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

theorem rowsChecked : CleanIdealRows.check babyBearModulus rowCapture = true := by decide +kernel
theorem checked : CleanIdealChecks.check babyBearModulus capture = true :=
  CleanIdealRows.check_sound babyBearModulus rowCapture sources rowsChecked
end Airbender.Compiler.CleanIdealNative.BlakeRoundUncached
