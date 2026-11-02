import Airbender.Proofs.GKRProtocol.HelperValidityChecks.ShiftBinopCached.Bindings

namespace Airbender.Compiler.HelperValidityChecks.ShiftBinopCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

theorem checked : NumericHelperValidityChecks.check babyBearModulus data = true := by decide +kernel

def facts :=
  NumericHelperValidityChecks.check_sound data Airbender.Compiler.HistoryErasureNative.ShiftBinopCached.native.historyCells
  Airbender.Compiler.HelperValidityNative.ShiftBinopCached.native.profile
  Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.helperPlacement Airbender.Compiler.SourceContractNative.ShiftBinopCached.native.slots
  Airbender.Compiler.HelperNative.ShiftBinopCached.native.fields Airbender.Compiler.HelperNative.ShiftBinopCached.native.placement
  Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.inputBank Airbender.Compiler.MemoryNative.ShiftBinopCached.native.bank
    source_binding checked

end Airbender.Compiler.HelperValidityChecks.ShiftBinopCached
