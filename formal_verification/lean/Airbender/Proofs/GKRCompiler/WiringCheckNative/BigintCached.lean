import Airbender.Proofs.GKRCompiler.WiringCheckNative.BigintCachedBindings

namespace Airbender.Compiler.WiringCheckNative.BigintCached
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

theorem checked : WiringChecks.check Airbender.Compiler.WiringNative.BigintCached.native.graph capture = true := by decide +kernel
theorem original_checked : (Airbender.Compiler.WiringNative.BigintCached.native.graph).check = true :=
  WiringChecks.check_sound Airbender.Compiler.WiringNative.BigintCached.native.graph capture bindings checked
end Airbender.Compiler.WiringCheckNative.BigintCached
