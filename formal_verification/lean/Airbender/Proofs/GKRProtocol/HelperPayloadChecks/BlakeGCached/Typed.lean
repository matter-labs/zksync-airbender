import Airbender.Proofs.GKRProtocol.HelperPayloadChecks.BlakeGCached.Inputs
import Airbender.Proofs.GKRProtocol.NumericNativePayloadChecks

namespace Airbender.Compiler.HelperPayloadChecks.BlakeGCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def originalEntries := [
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeGCached.native.candidate0
  Airbender.Compiler.HelperNative.BlakeGCached.native.placement Airbender.Compiler.MemoryNative.BlakeGCached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeGCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeGCached.native.candidate2
  Airbender.Compiler.HelperNative.BlakeGCached.native.placement Airbender.Compiler.MemoryNative.BlakeGCached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeGCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeGCached.native.candidate3
  Airbender.Compiler.HelperNative.BlakeGCached.native.placement Airbender.Compiler.MemoryNative.BlakeGCached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeGCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeGCached.native.candidate4
  Airbender.Compiler.HelperNative.BlakeGCached.native.placement Airbender.Compiler.MemoryNative.BlakeGCached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeGCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeGCached.native.candidate5
  Airbender.Compiler.HelperNative.BlakeGCached.native.placement Airbender.Compiler.MemoryNative.BlakeGCached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeGCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeGCached.native.candidate6
  Airbender.Compiler.HelperNative.BlakeGCached.native.placement Airbender.Compiler.MemoryNative.BlakeGCached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeGCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeGCached.native.candidate7
  Airbender.Compiler.HelperNative.BlakeGCached.native.placement Airbender.Compiler.MemoryNative.BlakeGCached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeGCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeGCached.native.candidate8
  Airbender.Compiler.HelperNative.BlakeGCached.native.placement Airbender.Compiler.MemoryNative.BlakeGCached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeGCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeGCached.native.candidate9
  Airbender.Compiler.HelperNative.BlakeGCached.native.placement Airbender.Compiler.MemoryNative.BlakeGCached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeGCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeGCached.native.candidate10
  Airbender.Compiler.HelperNative.BlakeGCached.native.placement Airbender.Compiler.MemoryNative.BlakeGCached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeGCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeGCached.native.candidate11
  Airbender.Compiler.HelperNative.BlakeGCached.native.placement Airbender.Compiler.MemoryNative.BlakeGCached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeGCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeGCached.native.candidate12
  Airbender.Compiler.HelperNative.BlakeGCached.native.placement Airbender.Compiler.MemoryNative.BlakeGCached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeGCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeGCached.native.candidate13
  Airbender.Compiler.HelperNative.BlakeGCached.native.placement Airbender.Compiler.MemoryNative.BlakeGCached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeGCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeGCached.native.candidate14
  Airbender.Compiler.HelperNative.BlakeGCached.native.placement Airbender.Compiler.MemoryNative.BlakeGCached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeGCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeGCached.native.candidate15
  Airbender.Compiler.HelperNative.BlakeGCached.native.placement Airbender.Compiler.MemoryNative.BlakeGCached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeGCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeGCached.native.candidate16
  Airbender.Compiler.HelperNative.BlakeGCached.native.placement Airbender.Compiler.MemoryNative.BlakeGCached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeGCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeGCached.native.candidate17
  Airbender.Compiler.HelperNative.BlakeGCached.native.placement Airbender.Compiler.MemoryNative.BlakeGCached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeGCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeGCached.native.candidate18
  Airbender.Compiler.HelperNative.BlakeGCached.native.placement Airbender.Compiler.MemoryNative.BlakeGCached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeGCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeGCached.native.candidate19
  Airbender.Compiler.HelperNative.BlakeGCached.native.placement Airbender.Compiler.MemoryNative.BlakeGCached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeGCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeGCached.native.candidate20
  Airbender.Compiler.HelperNative.BlakeGCached.native.placement Airbender.Compiler.MemoryNative.BlakeGCached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeGCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeGCached.native.candidate21
  Airbender.Compiler.HelperNative.BlakeGCached.native.placement Airbender.Compiler.MemoryNative.BlakeGCached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeGCached.native.typing]

end Airbender.Compiler.HelperPayloadChecks.BlakeGCached
