import Airbender.Proofs.GKRProtocol.HelperValidityChecks.BlakeGCached.Bindings

namespace Airbender.Compiler.HelperValidityChecks.BlakeGCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

theorem checked : NumericHelperValidityChecks.check babyBearModulus data = true := by decide +kernel

def facts :=
  NumericHelperValidityChecks.check_sound data Airbender.Compiler.HistoryErasureNative.BlakeGCached.native.historyCells
  Airbender.Compiler.HelperValidityNative.BlakeGCached.native.profile
  Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.helperPlacement Airbender.Compiler.SourceContractNative.BlakeGCached.native.slots
  Airbender.Compiler.HelperNative.BlakeGCached.native.fields Airbender.Compiler.HelperNative.BlakeGCached.native.placement
  Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.inputBank Airbender.Compiler.MemoryNative.BlakeGCached.native.bank
    source_binding checked

end Airbender.Compiler.HelperValidityChecks.BlakeGCached
