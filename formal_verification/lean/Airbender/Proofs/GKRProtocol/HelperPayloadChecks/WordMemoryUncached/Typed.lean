import Airbender.Proofs.GKRProtocol.HelperPayloadChecks.WordMemoryUncached.Inputs
import Airbender.Proofs.GKRProtocol.NumericNativePayloadChecks

namespace Airbender.Compiler.HelperPayloadChecks.WordMemoryUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def originalEntries := [
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.WordMemoryUncached.native.candidate2
  Airbender.Compiler.HelperNative.WordMemoryUncached.native.placement Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank
  Airbender.Compiler.ConsumerNative.WordMemoryUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.WordMemoryUncached.native.candidate4
  Airbender.Compiler.HelperNative.WordMemoryUncached.native.placement Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank
  Airbender.Compiler.ConsumerNative.WordMemoryUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.WordMemoryUncached.native.candidate5
  Airbender.Compiler.HelperNative.WordMemoryUncached.native.placement Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank
  Airbender.Compiler.ConsumerNative.WordMemoryUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.WordMemoryUncached.native.candidate6
  Airbender.Compiler.HelperNative.WordMemoryUncached.native.placement Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank
  Airbender.Compiler.ConsumerNative.WordMemoryUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.WordMemoryUncached.native.candidate7
  Airbender.Compiler.HelperNative.WordMemoryUncached.native.placement Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank
  Airbender.Compiler.ConsumerNative.WordMemoryUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.WordMemoryUncached.native.candidate8
  Airbender.Compiler.HelperNative.WordMemoryUncached.native.placement Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank
  Airbender.Compiler.ConsumerNative.WordMemoryUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.WordMemoryUncached.native.candidate9
  Airbender.Compiler.HelperNative.WordMemoryUncached.native.placement Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank
  Airbender.Compiler.ConsumerNative.WordMemoryUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.WordMemoryUncached.native.candidate13
  Airbender.Compiler.HelperNative.WordMemoryUncached.native.placement Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank
  Airbender.Compiler.ConsumerNative.WordMemoryUncached.native.typing]

end Airbender.Compiler.HelperPayloadChecks.WordMemoryUncached
