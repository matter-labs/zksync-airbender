import Airbender.Proofs.GKRProtocol.HelperValidityChecks.WordMemoryUncached.Bindings

namespace Airbender.Compiler.HelperValidityChecks.WordMemoryUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

theorem checked : NumericHelperValidityChecks.check babyBearModulus data = true := by decide +kernel

def facts :=
  NumericHelperValidityChecks.check_sound data Airbender.Compiler.HistoryErasureNative.WordMemoryUncached.native.historyCells
  Airbender.Compiler.HelperValidityNative.WordMemoryUncached.native.profile
  Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.helperPlacement Airbender.Compiler.SourceContractNative.WordMemoryUncached.native.slots
  Airbender.Compiler.HelperNative.WordMemoryUncached.native.fields Airbender.Compiler.HelperNative.WordMemoryUncached.native.placement
  Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.inputBank Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank
    source_binding checked

end Airbender.Compiler.HelperValidityChecks.WordMemoryUncached
