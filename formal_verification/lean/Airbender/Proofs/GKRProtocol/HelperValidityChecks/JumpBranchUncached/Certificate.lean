import Airbender.Proofs.GKRProtocol.HelperValidityChecks.JumpBranchUncached.Bindings

namespace Airbender.Compiler.HelperValidityChecks.JumpBranchUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

theorem checked : NumericHelperValidityChecks.check babyBearModulus data = true := by decide +kernel

def facts :=
  NumericHelperValidityChecks.check_sound data Airbender.Compiler.HistoryErasureNative.JumpBranchUncached.native.historyCells
  Airbender.Compiler.HelperValidityNative.JumpBranchUncached.native.profile
  Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.helperPlacement Airbender.Compiler.SourceContractNative.JumpBranchUncached.native.slots
  Airbender.Compiler.HelperNative.JumpBranchUncached.native.fields Airbender.Compiler.HelperNative.JumpBranchUncached.native.placement
  Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.inputBank Airbender.Compiler.MemoryNative.JumpBranchUncached.native.bank
    source_binding checked

end Airbender.Compiler.HelperValidityChecks.JumpBranchUncached
