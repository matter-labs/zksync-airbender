import Airbender.Proofs.GKRProtocol.HelperPayloadChecks.UnifiedUncached.Typed
import Airbender.Import.GKRProtocol.NumericFunctionalBaseImport

namespace Airbender.Compiler.HelperPayloadChecks.UnifiedUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

numeric_functional_base_capture data0 := [
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.UnifiedUncached.native.candidate12
  Airbender.Compiler.HelperNative.UnifiedUncached.native.placement Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank
  Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.UnifiedUncached.native.candidate14
  Airbender.Compiler.HelperNative.UnifiedUncached.native.placement Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank
  Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.UnifiedUncached.native.candidate15
  Airbender.Compiler.HelperNative.UnifiedUncached.native.placement Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank
  Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.UnifiedUncached.native.candidate16
  Airbender.Compiler.HelperNative.UnifiedUncached.native.placement Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank
  Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing)]

numeric_functional_base_capture data4 := [
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.UnifiedUncached.native.candidate17
  Airbender.Compiler.HelperNative.UnifiedUncached.native.placement Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank
  Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.UnifiedUncached.native.candidate18
  Airbender.Compiler.HelperNative.UnifiedUncached.native.placement Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank
  Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.UnifiedUncached.native.candidate19
  Airbender.Compiler.HelperNative.UnifiedUncached.native.placement Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank
  Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.UnifiedUncached.native.candidate24
  Airbender.Compiler.HelperNative.UnifiedUncached.native.placement Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank
  Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing)]

noncomputable def data : List NumericFunctionalBaseChecks.Data := (data0 ++ data4)

end Airbender.Compiler.HelperPayloadChecks.UnifiedUncached
