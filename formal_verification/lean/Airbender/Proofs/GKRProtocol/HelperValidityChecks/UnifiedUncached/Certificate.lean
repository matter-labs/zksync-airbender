import Airbender.Proofs.GKRProtocol.HelperValidityChecks.UnifiedUncached.Bindings

namespace Airbender.Compiler.HelperValidityChecks.UnifiedUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

theorem checked : NumericHelperValidityChecks.check babyBearModulus data = true := by decide +kernel

def facts :=
  NumericHelperValidityChecks.check_sound data Airbender.Compiler.HistoryErasureNative.UnifiedUncached.native.historyCells
  Airbender.Compiler.HelperValidityNative.UnifiedUncached.native.profile
  Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.helperPlacement Airbender.Compiler.SourceContractNative.UnifiedUncached.native.slots
  Airbender.Compiler.HelperNative.UnifiedUncached.native.fields Airbender.Compiler.HelperNative.UnifiedUncached.native.placement
  Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.inputBank Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank
    source_binding checked

end Airbender.Compiler.HelperValidityChecks.UnifiedUncached
