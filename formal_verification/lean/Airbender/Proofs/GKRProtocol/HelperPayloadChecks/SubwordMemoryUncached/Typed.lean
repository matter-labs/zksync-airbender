import Airbender.Proofs.GKRProtocol.HelperPayloadChecks.SubwordMemoryUncached.Inputs
import Airbender.Proofs.GKRProtocol.NumericNativePayloadChecks

namespace Airbender.Compiler.HelperPayloadChecks.SubwordMemoryUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def originalEntries := [
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.candidate4
  Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.placement Airbender.Compiler.MemoryNative.SubwordMemoryUncached.native.bank
  Airbender.Compiler.ConsumerNative.SubwordMemoryUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.candidate6
  Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.placement Airbender.Compiler.MemoryNative.SubwordMemoryUncached.native.bank
  Airbender.Compiler.ConsumerNative.SubwordMemoryUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.candidate7
  Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.placement Airbender.Compiler.MemoryNative.SubwordMemoryUncached.native.bank
  Airbender.Compiler.ConsumerNative.SubwordMemoryUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.candidate8
  Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.placement Airbender.Compiler.MemoryNative.SubwordMemoryUncached.native.bank
  Airbender.Compiler.ConsumerNative.SubwordMemoryUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.candidate9
  Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.placement Airbender.Compiler.MemoryNative.SubwordMemoryUncached.native.bank
  Airbender.Compiler.ConsumerNative.SubwordMemoryUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.candidate10
  Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.placement Airbender.Compiler.MemoryNative.SubwordMemoryUncached.native.bank
  Airbender.Compiler.ConsumerNative.SubwordMemoryUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.candidate11
  Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.placement Airbender.Compiler.MemoryNative.SubwordMemoryUncached.native.bank
  Airbender.Compiler.ConsumerNative.SubwordMemoryUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.candidate16
  Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.placement Airbender.Compiler.MemoryNative.SubwordMemoryUncached.native.bank
  Airbender.Compiler.ConsumerNative.SubwordMemoryUncached.native.typing]

end Airbender.Compiler.HelperPayloadChecks.SubwordMemoryUncached
