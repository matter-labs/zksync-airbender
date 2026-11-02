import Airbender.Proofs.GKRProtocol.HelperValidityChecks.BlakeRoundUncached.Bindings

namespace Airbender.Compiler.HelperValidityChecks.BlakeRoundUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

theorem checked : NumericHelperValidityChecks.check babyBearModulus data = true := by decide +kernel

def facts :=
  NumericHelperValidityChecks.check_sound data Airbender.Compiler.HistoryErasureNative.BlakeRoundUncached.native.historyCells
  Airbender.Compiler.HelperValidityNative.BlakeRoundUncached.native.profile
  Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.helperPlacement Airbender.Compiler.SourceContractNative.BlakeRoundUncached.native.slots
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.fields Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement
  Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.inputBank Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
    source_binding checked

end Airbender.Compiler.HelperValidityChecks.BlakeRoundUncached
