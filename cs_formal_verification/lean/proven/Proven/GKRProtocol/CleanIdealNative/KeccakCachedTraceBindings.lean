module
import all Mathlib.Data.List.Sort
public import Proven.GKRProtocol.CleanIdealNative.KeccakCachedBindings

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.CleanIdealNative.KeccakCached
set_option maxRecDepth 32768
theorem traceBindings : CleanIdealTrace.bindingCheck babyBearModulus traceCapture = true := by decide +kernel
end Airbender.Compiler.CleanIdealNative.KeccakCached
