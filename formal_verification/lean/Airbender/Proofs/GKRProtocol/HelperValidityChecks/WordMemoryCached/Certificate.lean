import Airbender.Proofs.GKRProtocol.HelperValidityChecks.WordMemoryCached.Bindings

namespace Airbender.Compiler.HelperValidityChecks.WordMemoryCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

theorem checked : NumericHelperValidityChecks.check babyBearModulus data = true := by decide +kernel

def facts :=
  NumericHelperValidityChecks.check_sound data Airbender.Compiler.HistoryErasureNative.WordMemoryCached.native.historyCells
  Airbender.Compiler.HelperValidityNative.WordMemoryCached.native.profile
  Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.helperPlacement Airbender.Compiler.SourceContractNative.WordMemoryCached.native.slots
  Airbender.Compiler.HelperNative.WordMemoryCached.native.fields Airbender.Compiler.HelperNative.WordMemoryCached.native.placement
  Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.inputBank Airbender.Compiler.MemoryNative.WordMemoryCached.native.bank
    source_binding checked

end Airbender.Compiler.HelperValidityChecks.WordMemoryCached
