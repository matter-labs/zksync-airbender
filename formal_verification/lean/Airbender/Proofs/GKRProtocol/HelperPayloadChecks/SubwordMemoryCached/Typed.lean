import Airbender.Proofs.GKRProtocol.HelperPayloadChecks.SubwordMemoryCached.Inputs
import Airbender.Proofs.GKRProtocol.NumericNativePayloadChecks

namespace Airbender.Compiler.HelperPayloadChecks.SubwordMemoryCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def originalEntries := [
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.SubwordMemoryCached.native.candidate4
  Airbender.Compiler.HelperNative.SubwordMemoryCached.native.placement Airbender.Compiler.MemoryNative.SubwordMemoryCached.native.bank
  Airbender.Compiler.ConsumerNative.SubwordMemoryCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.SubwordMemoryCached.native.candidate6
  Airbender.Compiler.HelperNative.SubwordMemoryCached.native.placement Airbender.Compiler.MemoryNative.SubwordMemoryCached.native.bank
  Airbender.Compiler.ConsumerNative.SubwordMemoryCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.SubwordMemoryCached.native.candidate7
  Airbender.Compiler.HelperNative.SubwordMemoryCached.native.placement Airbender.Compiler.MemoryNative.SubwordMemoryCached.native.bank
  Airbender.Compiler.ConsumerNative.SubwordMemoryCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.SubwordMemoryCached.native.candidate8
  Airbender.Compiler.HelperNative.SubwordMemoryCached.native.placement Airbender.Compiler.MemoryNative.SubwordMemoryCached.native.bank
  Airbender.Compiler.ConsumerNative.SubwordMemoryCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.SubwordMemoryCached.native.candidate9
  Airbender.Compiler.HelperNative.SubwordMemoryCached.native.placement Airbender.Compiler.MemoryNative.SubwordMemoryCached.native.bank
  Airbender.Compiler.ConsumerNative.SubwordMemoryCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.SubwordMemoryCached.native.candidate10
  Airbender.Compiler.HelperNative.SubwordMemoryCached.native.placement Airbender.Compiler.MemoryNative.SubwordMemoryCached.native.bank
  Airbender.Compiler.ConsumerNative.SubwordMemoryCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.SubwordMemoryCached.native.candidate11
  Airbender.Compiler.HelperNative.SubwordMemoryCached.native.placement Airbender.Compiler.MemoryNative.SubwordMemoryCached.native.bank
  Airbender.Compiler.ConsumerNative.SubwordMemoryCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.SubwordMemoryCached.native.candidate16
  Airbender.Compiler.HelperNative.SubwordMemoryCached.native.placement Airbender.Compiler.MemoryNative.SubwordMemoryCached.native.bank
  Airbender.Compiler.ConsumerNative.SubwordMemoryCached.native.typing]

end Airbender.Compiler.HelperPayloadChecks.SubwordMemoryCached
