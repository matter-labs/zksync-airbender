import Airbender.Proofs.GKRCompiler.WiringCheckNative.SubwordMemoryUncachedBindings

namespace Airbender.Compiler.WiringCheckNative.SubwordMemoryUncached
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

theorem checked : WiringChecks.check Airbender.Compiler.WiringNative.SubwordMemoryUncached.native.graph capture = true := by decide +kernel
theorem original_checked : (Airbender.Compiler.WiringNative.SubwordMemoryUncached.native.graph).check = true :=
  WiringChecks.check_sound Airbender.Compiler.WiringNative.SubwordMemoryUncached.native.graph capture bindings checked
end Airbender.Compiler.WiringCheckNative.SubwordMemoryUncached
