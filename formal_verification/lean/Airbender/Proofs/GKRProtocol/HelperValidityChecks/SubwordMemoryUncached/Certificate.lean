import Airbender.Proofs.GKRProtocol.HelperValidityChecks.SubwordMemoryUncached.Bindings

namespace Airbender.Compiler.HelperValidityChecks.SubwordMemoryUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

theorem checked : NumericHelperValidityChecks.check babyBearModulus data = true := by decide +kernel

def facts :=
  NumericHelperValidityChecks.check_sound data Airbender.Compiler.HistoryErasureNative.SubwordMemoryUncached.native.historyCells
  Airbender.Compiler.HelperValidityNative.SubwordMemoryUncached.native.profile
  Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.helperPlacement Airbender.Compiler.SourceContractNative.SubwordMemoryUncached.native.slots
  Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.fields Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.placement
  Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.inputBank Airbender.Compiler.MemoryNative.SubwordMemoryUncached.native.bank
    source_binding checked

end Airbender.Compiler.HelperValidityChecks.SubwordMemoryUncached
