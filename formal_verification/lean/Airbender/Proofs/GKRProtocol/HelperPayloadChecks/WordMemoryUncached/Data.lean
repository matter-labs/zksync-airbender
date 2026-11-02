import Airbender.Proofs.GKRProtocol.HelperPayloadChecks.WordMemoryUncached.Typed
import Airbender.Import.GKRProtocol.NumericFunctionalBaseImport

namespace Airbender.Compiler.HelperPayloadChecks.WordMemoryUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

numeric_functional_base_capture data0 := [
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.WordMemoryUncached.native.candidate2
  Airbender.Compiler.HelperNative.WordMemoryUncached.native.placement Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank
  Airbender.Compiler.ConsumerNative.WordMemoryUncached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.WordMemoryUncached.native.candidate4
  Airbender.Compiler.HelperNative.WordMemoryUncached.native.placement Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank
  Airbender.Compiler.ConsumerNative.WordMemoryUncached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.WordMemoryUncached.native.candidate5
  Airbender.Compiler.HelperNative.WordMemoryUncached.native.placement Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank
  Airbender.Compiler.ConsumerNative.WordMemoryUncached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.WordMemoryUncached.native.candidate6
  Airbender.Compiler.HelperNative.WordMemoryUncached.native.placement Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank
  Airbender.Compiler.ConsumerNative.WordMemoryUncached.native.typing)]

numeric_functional_base_capture data4 := [
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.WordMemoryUncached.native.candidate7
  Airbender.Compiler.HelperNative.WordMemoryUncached.native.placement Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank
  Airbender.Compiler.ConsumerNative.WordMemoryUncached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.WordMemoryUncached.native.candidate8
  Airbender.Compiler.HelperNative.WordMemoryUncached.native.placement Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank
  Airbender.Compiler.ConsumerNative.WordMemoryUncached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.WordMemoryUncached.native.candidate9
  Airbender.Compiler.HelperNative.WordMemoryUncached.native.placement Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank
  Airbender.Compiler.ConsumerNative.WordMemoryUncached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.WordMemoryUncached.native.candidate13
  Airbender.Compiler.HelperNative.WordMemoryUncached.native.placement Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank
  Airbender.Compiler.ConsumerNative.WordMemoryUncached.native.typing)]

noncomputable def data : List NumericFunctionalBaseChecks.Data := (data0 ++ data4)

end Airbender.Compiler.HelperPayloadChecks.WordMemoryUncached
