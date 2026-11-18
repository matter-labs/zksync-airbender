module
import all Mathlib.Data.List.Sort
public import Proven.GKRProtocol.HelperPayloadChecks.UnifiedCached.Inputs
public import Proven.GKRProtocol.NumericNativePayloadChecks

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.HelperPayloadChecks.UnifiedCached
open Airbender Airbender.Compiler
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
