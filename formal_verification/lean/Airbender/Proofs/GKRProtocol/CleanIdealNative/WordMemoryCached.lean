import Airbender.Proofs.GKRProtocol.CleanIdealNative.WordMemoryCachedData

namespace Airbender.Compiler.CleanIdealNative.WordMemoryCached
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

theorem checked : CleanIdealChecks.check babyBearModulus capture = true := by decide +kernel

end Airbender.Compiler.CleanIdealNative.WordMemoryCached
