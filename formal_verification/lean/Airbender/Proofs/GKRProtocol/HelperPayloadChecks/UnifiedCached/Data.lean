import Airbender.Proofs.GKRProtocol.HelperPayloadChecks.UnifiedCached.Typed
import Airbender.Import.GKRProtocol.NumericFunctionalBaseImport

namespace Airbender.Compiler.HelperPayloadChecks.UnifiedCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

numeric_functional_base_capture data0 := [
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.UnifiedCached.native.candidate12
  Airbender.Compiler.HelperNative.UnifiedCached.native.placement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank
  Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.UnifiedCached.native.candidate14
  Airbender.Compiler.HelperNative.UnifiedCached.native.placement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank
  Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.UnifiedCached.native.candidate15
  Airbender.Compiler.HelperNative.UnifiedCached.native.placement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank
  Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.UnifiedCached.native.candidate16
  Airbender.Compiler.HelperNative.UnifiedCached.native.placement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank
  Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing)]

numeric_functional_base_capture data4 := [
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.UnifiedCached.native.candidate17
  Airbender.Compiler.HelperNative.UnifiedCached.native.placement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank
  Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.UnifiedCached.native.candidate18
  Airbender.Compiler.HelperNative.UnifiedCached.native.placement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank
  Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.UnifiedCached.native.candidate19
  Airbender.Compiler.HelperNative.UnifiedCached.native.placement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank
  Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.UnifiedCached.native.candidate24
  Airbender.Compiler.HelperNative.UnifiedCached.native.placement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank
  Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing)]

noncomputable def data : List NumericFunctionalBaseChecks.Data := (data0 ++ data4)

end Airbender.Compiler.HelperPayloadChecks.UnifiedCached
