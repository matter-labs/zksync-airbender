import Airbender.Proofs.GKRProtocol.CleanIdealNative.KeccakUncachedBindings

namespace Airbender.Compiler.CleanIdealNative.KeccakUncached
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
theorem traceBindings : CleanIdealTrace.bindingCheck babyBearModulus traceCapture = true := by decide +kernel
end Airbender.Compiler.CleanIdealNative.KeccakUncached
