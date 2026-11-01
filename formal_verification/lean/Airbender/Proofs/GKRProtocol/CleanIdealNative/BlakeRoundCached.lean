import Airbender.Proofs.GKRProtocol.CleanIdealNative.BlakeRoundCachedBindings

namespace Airbender.Compiler.CleanIdealNative.BlakeRoundCached
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

theorem rowsChecked : CleanIdealRows.check babyBearModulus rowCapture = true := by decide +kernel
theorem checked : CleanIdealChecks.check babyBearModulus capture = true :=
  CleanIdealRows.check_sound babyBearModulus rowCapture sources rowsChecked
end Airbender.Compiler.CleanIdealNative.BlakeRoundCached
