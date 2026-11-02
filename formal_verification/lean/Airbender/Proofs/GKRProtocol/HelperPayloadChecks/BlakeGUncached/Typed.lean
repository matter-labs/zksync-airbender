import Airbender.Proofs.GKRProtocol.HelperPayloadChecks.BlakeGUncached.Inputs
import Airbender.Proofs.GKRProtocol.NumericNativePayloadChecks

namespace Airbender.Compiler.HelperPayloadChecks.BlakeGUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def originalEntries := [
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeGUncached.native.candidate0
  Airbender.Compiler.HelperNative.BlakeGUncached.native.placement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeGUncached.native.candidate2
  Airbender.Compiler.HelperNative.BlakeGUncached.native.placement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeGUncached.native.candidate3
  Airbender.Compiler.HelperNative.BlakeGUncached.native.placement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeGUncached.native.candidate4
  Airbender.Compiler.HelperNative.BlakeGUncached.native.placement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeGUncached.native.candidate5
  Airbender.Compiler.HelperNative.BlakeGUncached.native.placement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeGUncached.native.candidate6
  Airbender.Compiler.HelperNative.BlakeGUncached.native.placement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeGUncached.native.candidate7
  Airbender.Compiler.HelperNative.BlakeGUncached.native.placement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeGUncached.native.candidate8
  Airbender.Compiler.HelperNative.BlakeGUncached.native.placement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeGUncached.native.candidate9
  Airbender.Compiler.HelperNative.BlakeGUncached.native.placement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeGUncached.native.candidate10
  Airbender.Compiler.HelperNative.BlakeGUncached.native.placement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeGUncached.native.candidate11
  Airbender.Compiler.HelperNative.BlakeGUncached.native.placement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeGUncached.native.candidate12
  Airbender.Compiler.HelperNative.BlakeGUncached.native.placement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeGUncached.native.candidate13
  Airbender.Compiler.HelperNative.BlakeGUncached.native.placement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeGUncached.native.candidate14
  Airbender.Compiler.HelperNative.BlakeGUncached.native.placement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeGUncached.native.candidate15
  Airbender.Compiler.HelperNative.BlakeGUncached.native.placement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeGUncached.native.candidate16
  Airbender.Compiler.HelperNative.BlakeGUncached.native.placement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeGUncached.native.candidate17
  Airbender.Compiler.HelperNative.BlakeGUncached.native.placement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeGUncached.native.candidate18
  Airbender.Compiler.HelperNative.BlakeGUncached.native.placement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeGUncached.native.candidate19
  Airbender.Compiler.HelperNative.BlakeGUncached.native.placement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeGUncached.native.candidate20
  Airbender.Compiler.HelperNative.BlakeGUncached.native.placement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeGUncached.native.candidate21
  Airbender.Compiler.HelperNative.BlakeGUncached.native.placement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing]

end Airbender.Compiler.HelperPayloadChecks.BlakeGUncached
