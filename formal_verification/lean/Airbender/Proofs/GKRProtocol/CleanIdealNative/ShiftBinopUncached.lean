import Airbender.Proofs.GKRProtocol.CleanIdealNative.ShiftBinopUncachedData

namespace Airbender.Compiler.CleanIdealNative.ShiftBinopUncached
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

theorem checked : CleanIdealChecks.check babyBearModulus capture = true := by decide +kernel

end Airbender.Compiler.CleanIdealNative.ShiftBinopUncached
