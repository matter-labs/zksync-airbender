import Airbender.Proofs.GKRProtocol.HelperPayloadChecks.SubwordMemoryUncached.Typed
import Airbender.Import.GKRProtocol.NumericFunctionalBaseImport

namespace Airbender.Compiler.HelperPayloadChecks.SubwordMemoryUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

numeric_functional_base_capture data0 := [
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.candidate4
  Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.placement Airbender.Compiler.MemoryNative.SubwordMemoryUncached.native.bank
  Airbender.Compiler.ConsumerNative.SubwordMemoryUncached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.candidate6
  Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.placement Airbender.Compiler.MemoryNative.SubwordMemoryUncached.native.bank
  Airbender.Compiler.ConsumerNative.SubwordMemoryUncached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.candidate7
  Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.placement Airbender.Compiler.MemoryNative.SubwordMemoryUncached.native.bank
  Airbender.Compiler.ConsumerNative.SubwordMemoryUncached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.candidate8
  Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.placement Airbender.Compiler.MemoryNative.SubwordMemoryUncached.native.bank
  Airbender.Compiler.ConsumerNative.SubwordMemoryUncached.native.typing)]

numeric_functional_base_capture data4 := [
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.candidate9
  Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.placement Airbender.Compiler.MemoryNative.SubwordMemoryUncached.native.bank
  Airbender.Compiler.ConsumerNative.SubwordMemoryUncached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.candidate10
  Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.placement Airbender.Compiler.MemoryNative.SubwordMemoryUncached.native.bank
  Airbender.Compiler.ConsumerNative.SubwordMemoryUncached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.candidate11
  Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.placement Airbender.Compiler.MemoryNative.SubwordMemoryUncached.native.bank
  Airbender.Compiler.ConsumerNative.SubwordMemoryUncached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.candidate16
  Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.placement Airbender.Compiler.MemoryNative.SubwordMemoryUncached.native.bank
  Airbender.Compiler.ConsumerNative.SubwordMemoryUncached.native.typing)]

noncomputable def data : List NumericFunctionalBaseChecks.Data := (data0 ++ data4)

end Airbender.Compiler.HelperPayloadChecks.SubwordMemoryUncached
