import Airbender.Proofs.GKRProtocol.HelperValidityChecks.UnifiedCached.Bindings

namespace Airbender.Compiler.HelperValidityChecks.UnifiedCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

theorem checked : NumericHelperValidityChecks.check babyBearModulus data = true := by decide +kernel

def facts :=
  NumericHelperValidityChecks.check_sound data Airbender.Compiler.HistoryErasureNative.UnifiedCached.native.historyCells
  Airbender.Compiler.HelperValidityNative.UnifiedCached.native.profile
  Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.helperPlacement Airbender.Compiler.SourceContractNative.UnifiedCached.native.slots
  Airbender.Compiler.HelperNative.UnifiedCached.native.fields Airbender.Compiler.HelperNative.UnifiedCached.native.placement
  Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.inputBank Airbender.Compiler.MemoryNative.UnifiedCached.native.bank
    source_binding checked

end Airbender.Compiler.HelperValidityChecks.UnifiedCached
