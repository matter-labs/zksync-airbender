import Airbender.Proofs.GKRProtocol.HelperPayloadChecks.WordMemoryCached.Inputs
import Airbender.Proofs.GKRProtocol.NumericNativePayloadChecks

namespace Airbender.Compiler.HelperPayloadChecks.WordMemoryCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def originalEntries := [
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.WordMemoryCached.native.candidate2
  Airbender.Compiler.HelperNative.WordMemoryCached.native.placement Airbender.Compiler.MemoryNative.WordMemoryCached.native.bank
  Airbender.Compiler.ConsumerNative.WordMemoryCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.WordMemoryCached.native.candidate4
  Airbender.Compiler.HelperNative.WordMemoryCached.native.placement Airbender.Compiler.MemoryNative.WordMemoryCached.native.bank
  Airbender.Compiler.ConsumerNative.WordMemoryCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.WordMemoryCached.native.candidate5
  Airbender.Compiler.HelperNative.WordMemoryCached.native.placement Airbender.Compiler.MemoryNative.WordMemoryCached.native.bank
  Airbender.Compiler.ConsumerNative.WordMemoryCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.WordMemoryCached.native.candidate6
  Airbender.Compiler.HelperNative.WordMemoryCached.native.placement Airbender.Compiler.MemoryNative.WordMemoryCached.native.bank
  Airbender.Compiler.ConsumerNative.WordMemoryCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.WordMemoryCached.native.candidate7
  Airbender.Compiler.HelperNative.WordMemoryCached.native.placement Airbender.Compiler.MemoryNative.WordMemoryCached.native.bank
  Airbender.Compiler.ConsumerNative.WordMemoryCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.WordMemoryCached.native.candidate8
  Airbender.Compiler.HelperNative.WordMemoryCached.native.placement Airbender.Compiler.MemoryNative.WordMemoryCached.native.bank
  Airbender.Compiler.ConsumerNative.WordMemoryCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.WordMemoryCached.native.candidate9
  Airbender.Compiler.HelperNative.WordMemoryCached.native.placement Airbender.Compiler.MemoryNative.WordMemoryCached.native.bank
  Airbender.Compiler.ConsumerNative.WordMemoryCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.WordMemoryCached.native.candidate13
  Airbender.Compiler.HelperNative.WordMemoryCached.native.placement Airbender.Compiler.MemoryNative.WordMemoryCached.native.bank
  Airbender.Compiler.ConsumerNative.WordMemoryCached.native.typing]

end Airbender.Compiler.HelperPayloadChecks.WordMemoryCached
