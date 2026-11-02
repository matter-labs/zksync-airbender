import Airbender.Proofs.GKRProtocol.HelperPayloadChecks.AddSubUncached.Typed
import Airbender.Import.GKRProtocol.NumericFunctionalBaseImport

namespace Airbender.Compiler.HelperPayloadChecks.AddSubUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

numeric_functional_base_capture data0 := [
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.AddSubUncached.native.candidate6
  Airbender.Compiler.HelperNative.AddSubUncached.native.placement Airbender.Compiler.MemoryNative.AddSubUncached.native.bank
  Airbender.Compiler.ConsumerNative.AddSubUncached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.AddSubUncached.native.candidate8
  Airbender.Compiler.HelperNative.AddSubUncached.native.placement Airbender.Compiler.MemoryNative.AddSubUncached.native.bank
  Airbender.Compiler.ConsumerNative.AddSubUncached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.AddSubUncached.native.candidate9
  Airbender.Compiler.HelperNative.AddSubUncached.native.placement Airbender.Compiler.MemoryNative.AddSubUncached.native.bank
  Airbender.Compiler.ConsumerNative.AddSubUncached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.AddSubUncached.native.candidate10
  Airbender.Compiler.HelperNative.AddSubUncached.native.placement Airbender.Compiler.MemoryNative.AddSubUncached.native.bank
  Airbender.Compiler.ConsumerNative.AddSubUncached.native.typing)]

numeric_functional_base_capture data4 := [
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.AddSubUncached.native.candidate11
  Airbender.Compiler.HelperNative.AddSubUncached.native.placement Airbender.Compiler.MemoryNative.AddSubUncached.native.bank
  Airbender.Compiler.ConsumerNative.AddSubUncached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.AddSubUncached.native.candidate12
  Airbender.Compiler.HelperNative.AddSubUncached.native.placement Airbender.Compiler.MemoryNative.AddSubUncached.native.bank
  Airbender.Compiler.ConsumerNative.AddSubUncached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.AddSubUncached.native.candidate13
  Airbender.Compiler.HelperNative.AddSubUncached.native.placement Airbender.Compiler.MemoryNative.AddSubUncached.native.bank
  Airbender.Compiler.ConsumerNative.AddSubUncached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.AddSubUncached.native.candidate17
  Airbender.Compiler.HelperNative.AddSubUncached.native.placement Airbender.Compiler.MemoryNative.AddSubUncached.native.bank
  Airbender.Compiler.ConsumerNative.AddSubUncached.native.typing)]

noncomputable def data : List NumericFunctionalBaseChecks.Data := (data0 ++ data4)

end Airbender.Compiler.HelperPayloadChecks.AddSubUncached
