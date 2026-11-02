import Airbender.Proofs.GKRProtocol.HelperValidityChecks.BlakeRoundCached.Bindings

namespace Airbender.Compiler.HelperValidityChecks.BlakeRoundCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

theorem checked : NumericHelperValidityChecks.check babyBearModulus data = true := by decide +kernel

def facts :=
  NumericHelperValidityChecks.check_sound data Airbender.Compiler.HistoryErasureNative.BlakeRoundCached.native.historyCells
  Airbender.Compiler.HelperValidityNative.BlakeRoundCached.native.profile
  Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.helperPlacement Airbender.Compiler.SourceContractNative.BlakeRoundCached.native.slots
  Airbender.Compiler.HelperNative.BlakeRoundCached.native.fields Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement
  Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.inputBank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank
    source_binding checked

end Airbender.Compiler.HelperValidityChecks.BlakeRoundCached
