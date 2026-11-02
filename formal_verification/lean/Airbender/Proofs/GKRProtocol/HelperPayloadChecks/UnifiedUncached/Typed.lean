import Airbender.Proofs.GKRProtocol.HelperPayloadChecks.UnifiedUncached.Inputs
import Airbender.Proofs.GKRProtocol.NumericNativePayloadChecks

namespace Airbender.Compiler.HelperPayloadChecks.UnifiedUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def originalEntries := [
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.UnifiedUncached.native.candidate12
  Airbender.Compiler.HelperNative.UnifiedUncached.native.placement Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank
  Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.UnifiedUncached.native.candidate14
  Airbender.Compiler.HelperNative.UnifiedUncached.native.placement Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank
  Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.UnifiedUncached.native.candidate15
  Airbender.Compiler.HelperNative.UnifiedUncached.native.placement Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank
  Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.UnifiedUncached.native.candidate16
  Airbender.Compiler.HelperNative.UnifiedUncached.native.placement Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank
  Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.UnifiedUncached.native.candidate17
  Airbender.Compiler.HelperNative.UnifiedUncached.native.placement Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank
  Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.UnifiedUncached.native.candidate18
  Airbender.Compiler.HelperNative.UnifiedUncached.native.placement Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank
  Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.UnifiedUncached.native.candidate19
  Airbender.Compiler.HelperNative.UnifiedUncached.native.placement Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank
  Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.UnifiedUncached.native.candidate24
  Airbender.Compiler.HelperNative.UnifiedUncached.native.placement Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank
  Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing]

end Airbender.Compiler.HelperPayloadChecks.UnifiedUncached
