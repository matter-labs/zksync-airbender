import Airbender.Proofs.GKRProtocol.CleanIdealNative.BigintUncachedTraceBindings

namespace Airbender.Compiler.CleanIdealNative.BigintUncached
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

theorem traceChecked : CleanIdealTrace.check babyBearModulus traceCapture = true := by decide +kernel
theorem checked : CleanIdealChecks.check babyBearModulus capture = true :=
  CleanIdealTrace.check_sound babyBearModulus traceCapture sources traceBindings traceChecked

end Airbender.Compiler.CleanIdealNative.BigintUncached
