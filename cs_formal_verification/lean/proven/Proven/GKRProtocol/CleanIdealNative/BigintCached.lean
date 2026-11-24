module
import all Mathlib.Data.List.Sort
public import Proven.GKRProtocol.CleanIdealNative.BigintCachedTraceBindings

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.CleanIdealNative.BigintCached
set_option maxRecDepth 32768

theorem traceChecked : CleanIdealTrace.check babyBearModulus traceCapture = true := by decide +kernel
theorem checked : CleanIdealChecks.check babyBearModulus capture = true :=
  CleanIdealTrace.check_sound babyBearModulus traceCapture sources traceBindings traceChecked

end Airbender.Compiler.CleanIdealNative.BigintCached
