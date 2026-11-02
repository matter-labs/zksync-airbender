import Airbender.Proofs.GKRProtocol.HelperPayloadChecks.UnifiedCached.Inputs
import Airbender.Proofs.GKRProtocol.NumericNativePayloadChecks

namespace Airbender.Compiler.HelperPayloadChecks.UnifiedCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def originalEntries := [
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.UnifiedCached.native.candidate12
  Airbender.Compiler.HelperNative.UnifiedCached.native.placement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank
  Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.UnifiedCached.native.candidate14
  Airbender.Compiler.HelperNative.UnifiedCached.native.placement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank
  Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.UnifiedCached.native.candidate15
  Airbender.Compiler.HelperNative.UnifiedCached.native.placement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank
  Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.UnifiedCached.native.candidate16
  Airbender.Compiler.HelperNative.UnifiedCached.native.placement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank
  Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.UnifiedCached.native.candidate17
  Airbender.Compiler.HelperNative.UnifiedCached.native.placement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank
  Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.UnifiedCached.native.candidate18
  Airbender.Compiler.HelperNative.UnifiedCached.native.placement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank
  Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.UnifiedCached.native.candidate19
  Airbender.Compiler.HelperNative.UnifiedCached.native.placement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank
  Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.UnifiedCached.native.candidate24
  Airbender.Compiler.HelperNative.UnifiedCached.native.placement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank
  Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing]

end Airbender.Compiler.HelperPayloadChecks.UnifiedCached
