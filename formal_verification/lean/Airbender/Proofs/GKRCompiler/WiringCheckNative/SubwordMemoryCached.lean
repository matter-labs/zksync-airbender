import Airbender.Proofs.GKRCompiler.WiringCheckNative.SubwordMemoryCachedBindings

namespace Airbender.Compiler.WiringCheckNative.SubwordMemoryCached
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

theorem checked : WiringChecks.check Airbender.Compiler.WiringNative.SubwordMemoryCached.native.graph capture = true := by decide +kernel
theorem original_checked : (Airbender.Compiler.WiringNative.SubwordMemoryCached.native.graph).check = true :=
  WiringChecks.check_sound Airbender.Compiler.WiringNative.SubwordMemoryCached.native.graph capture bindings checked
end Airbender.Compiler.WiringCheckNative.SubwordMemoryCached
