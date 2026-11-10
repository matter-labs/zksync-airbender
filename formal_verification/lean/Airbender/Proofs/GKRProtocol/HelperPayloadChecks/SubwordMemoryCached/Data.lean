import Airbender.Proofs.GKRProtocol.HelperPayloadChecks.SubwordMemoryCached.Typed
import Airbender.Import.GKRProtocol.NumericFunctionalBaseImport

namespace Airbender.Compiler.HelperPayloadChecks.SubwordMemoryCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

numeric_functional_base_capture data0 := [
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.SubwordMemoryCached.native.candidate4
  Airbender.Compiler.HelperNative.SubwordMemoryCached.native.placement Airbender.Compiler.MemoryNative.SubwordMemoryCached.native.bank
  Airbender.Compiler.ConsumerNative.SubwordMemoryCached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.SubwordMemoryCached.native.candidate6
  Airbender.Compiler.HelperNative.SubwordMemoryCached.native.placement Airbender.Compiler.MemoryNative.SubwordMemoryCached.native.bank
  Airbender.Compiler.ConsumerNative.SubwordMemoryCached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.SubwordMemoryCached.native.candidate7
  Airbender.Compiler.HelperNative.SubwordMemoryCached.native.placement Airbender.Compiler.MemoryNative.SubwordMemoryCached.native.bank
  Airbender.Compiler.ConsumerNative.SubwordMemoryCached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.SubwordMemoryCached.native.candidate8
  Airbender.Compiler.HelperNative.SubwordMemoryCached.native.placement Airbender.Compiler.MemoryNative.SubwordMemoryCached.native.bank
  Airbender.Compiler.ConsumerNative.SubwordMemoryCached.native.typing)]

numeric_functional_base_capture data4 := [
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.SubwordMemoryCached.native.candidate9
  Airbender.Compiler.HelperNative.SubwordMemoryCached.native.placement Airbender.Compiler.MemoryNative.SubwordMemoryCached.native.bank
  Airbender.Compiler.ConsumerNative.SubwordMemoryCached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.SubwordMemoryCached.native.candidate10
  Airbender.Compiler.HelperNative.SubwordMemoryCached.native.placement Airbender.Compiler.MemoryNative.SubwordMemoryCached.native.bank
  Airbender.Compiler.ConsumerNative.SubwordMemoryCached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.SubwordMemoryCached.native.candidate11
  Airbender.Compiler.HelperNative.SubwordMemoryCached.native.placement Airbender.Compiler.MemoryNative.SubwordMemoryCached.native.bank
  Airbender.Compiler.ConsumerNative.SubwordMemoryCached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.SubwordMemoryCached.native.candidate16
  Airbender.Compiler.HelperNative.SubwordMemoryCached.native.placement Airbender.Compiler.MemoryNative.SubwordMemoryCached.native.bank
  Airbender.Compiler.ConsumerNative.SubwordMemoryCached.native.typing)]

noncomputable def data : List NumericFunctionalBaseChecks.Data := (data0 ++ data4)

end Airbender.Compiler.HelperPayloadChecks.SubwordMemoryCached
