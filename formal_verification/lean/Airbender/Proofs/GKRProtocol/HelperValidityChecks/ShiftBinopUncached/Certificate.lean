import Airbender.Proofs.GKRProtocol.HelperValidityChecks.ShiftBinopUncached.Bindings

namespace Airbender.Compiler.HelperValidityChecks.ShiftBinopUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

theorem checked : NumericHelperValidityChecks.check babyBearModulus data = true := by decide +kernel

def facts :=
  NumericHelperValidityChecks.check_sound data Airbender.Compiler.HistoryErasureNative.ShiftBinopUncached.native.historyCells
  Airbender.Compiler.HelperValidityNative.ShiftBinopUncached.native.profile
  Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.helperPlacement Airbender.Compiler.SourceContractNative.ShiftBinopUncached.native.slots
  Airbender.Compiler.HelperNative.ShiftBinopUncached.native.fields Airbender.Compiler.HelperNative.ShiftBinopUncached.native.placement
  Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.inputBank Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.bank
    source_binding checked

end Airbender.Compiler.HelperValidityChecks.ShiftBinopUncached
