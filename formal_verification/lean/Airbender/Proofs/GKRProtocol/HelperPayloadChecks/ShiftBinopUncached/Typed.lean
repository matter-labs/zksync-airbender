import Airbender.Proofs.GKRProtocol.HelperPayloadChecks.ShiftBinopUncached.Inputs
import Airbender.Proofs.GKRProtocol.NumericNativePayloadChecks

namespace Airbender.Compiler.HelperPayloadChecks.ShiftBinopUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def originalEntries := [
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.ShiftBinopUncached.native.candidate2
  Airbender.Compiler.HelperNative.ShiftBinopUncached.native.placement Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.bank
  Airbender.Compiler.ConsumerNative.ShiftBinopUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.ShiftBinopUncached.native.candidate4
  Airbender.Compiler.HelperNative.ShiftBinopUncached.native.placement Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.bank
  Airbender.Compiler.ConsumerNative.ShiftBinopUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.ShiftBinopUncached.native.candidate5
  Airbender.Compiler.HelperNative.ShiftBinopUncached.native.placement Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.bank
  Airbender.Compiler.ConsumerNative.ShiftBinopUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.ShiftBinopUncached.native.candidate6
  Airbender.Compiler.HelperNative.ShiftBinopUncached.native.placement Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.bank
  Airbender.Compiler.ConsumerNative.ShiftBinopUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.ShiftBinopUncached.native.candidate7
  Airbender.Compiler.HelperNative.ShiftBinopUncached.native.placement Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.bank
  Airbender.Compiler.ConsumerNative.ShiftBinopUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.ShiftBinopUncached.native.candidate8
  Airbender.Compiler.HelperNative.ShiftBinopUncached.native.placement Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.bank
  Airbender.Compiler.ConsumerNative.ShiftBinopUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.ShiftBinopUncached.native.candidate9
  Airbender.Compiler.HelperNative.ShiftBinopUncached.native.placement Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.bank
  Airbender.Compiler.ConsumerNative.ShiftBinopUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.ShiftBinopUncached.native.candidate13
  Airbender.Compiler.HelperNative.ShiftBinopUncached.native.placement Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.bank
  Airbender.Compiler.ConsumerNative.ShiftBinopUncached.native.typing]

end Airbender.Compiler.HelperPayloadChecks.ShiftBinopUncached
