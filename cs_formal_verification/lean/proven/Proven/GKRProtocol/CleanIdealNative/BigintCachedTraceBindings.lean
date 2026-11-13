module
import all Mathlib.Data.List.Sort
public import Proven.GKRProtocol.CleanIdealNative.BigintCachedBindings

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.CleanIdealNative.BigintCached
set_option maxRecDepth 32768
theorem traceBindings : CleanIdealTrace.bindingCheck babyBearModulus traceCapture = true := by decide +kernel
end Airbender.Compiler.CleanIdealNative.BigintCached
