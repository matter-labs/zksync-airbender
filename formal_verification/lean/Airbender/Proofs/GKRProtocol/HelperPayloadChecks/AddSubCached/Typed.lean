import Airbender.Proofs.GKRProtocol.HelperPayloadChecks.AddSubCached.Inputs
import Airbender.Proofs.GKRProtocol.NumericNativePayloadChecks

namespace Airbender.Compiler.HelperPayloadChecks.AddSubCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def originalEntries := [
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.AddSubCached.native.candidate6
  Airbender.Compiler.HelperNative.AddSubCached.native.placement Airbender.Compiler.MemoryNative.AddSubCached.native.bank
  Airbender.Compiler.ConsumerNative.AddSubCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.AddSubCached.native.candidate8
  Airbender.Compiler.HelperNative.AddSubCached.native.placement Airbender.Compiler.MemoryNative.AddSubCached.native.bank
  Airbender.Compiler.ConsumerNative.AddSubCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.AddSubCached.native.candidate9
  Airbender.Compiler.HelperNative.AddSubCached.native.placement Airbender.Compiler.MemoryNative.AddSubCached.native.bank
  Airbender.Compiler.ConsumerNative.AddSubCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.AddSubCached.native.candidate10
  Airbender.Compiler.HelperNative.AddSubCached.native.placement Airbender.Compiler.MemoryNative.AddSubCached.native.bank
  Airbender.Compiler.ConsumerNative.AddSubCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.AddSubCached.native.candidate11
  Airbender.Compiler.HelperNative.AddSubCached.native.placement Airbender.Compiler.MemoryNative.AddSubCached.native.bank
  Airbender.Compiler.ConsumerNative.AddSubCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.AddSubCached.native.candidate12
  Airbender.Compiler.HelperNative.AddSubCached.native.placement Airbender.Compiler.MemoryNative.AddSubCached.native.bank
  Airbender.Compiler.ConsumerNative.AddSubCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.AddSubCached.native.candidate13
  Airbender.Compiler.HelperNative.AddSubCached.native.placement Airbender.Compiler.MemoryNative.AddSubCached.native.bank
  Airbender.Compiler.ConsumerNative.AddSubCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.AddSubCached.native.candidate17
  Airbender.Compiler.HelperNative.AddSubCached.native.placement Airbender.Compiler.MemoryNative.AddSubCached.native.bank
  Airbender.Compiler.ConsumerNative.AddSubCached.native.typing]

end Airbender.Compiler.HelperPayloadChecks.AddSubCached
