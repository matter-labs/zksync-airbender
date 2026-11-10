import Airbender.Proofs.GKRProtocol.HelperPayloadChecks.MulDivCached.Typed
import Airbender.Import.GKRProtocol.NumericFunctionalBaseImport

namespace Airbender.Compiler.HelperPayloadChecks.MulDivCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

numeric_functional_base_capture data0 := [
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.MulDivCached.native.candidate8
  Airbender.Compiler.HelperNative.MulDivCached.native.placement Airbender.Compiler.MemoryNative.MulDivCached.native.bank
  Airbender.Compiler.ConsumerNative.MulDivCached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.MulDivCached.native.candidate10
  Airbender.Compiler.HelperNative.MulDivCached.native.placement Airbender.Compiler.MemoryNative.MulDivCached.native.bank
  Airbender.Compiler.ConsumerNative.MulDivCached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.MulDivCached.native.candidate11
  Airbender.Compiler.HelperNative.MulDivCached.native.placement Airbender.Compiler.MemoryNative.MulDivCached.native.bank
  Airbender.Compiler.ConsumerNative.MulDivCached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.MulDivCached.native.candidate12
  Airbender.Compiler.HelperNative.MulDivCached.native.placement Airbender.Compiler.MemoryNative.MulDivCached.native.bank
  Airbender.Compiler.ConsumerNative.MulDivCached.native.typing)]

numeric_functional_base_capture data4 := [
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.MulDivCached.native.candidate13
  Airbender.Compiler.HelperNative.MulDivCached.native.placement Airbender.Compiler.MemoryNative.MulDivCached.native.bank
  Airbender.Compiler.ConsumerNative.MulDivCached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.MulDivCached.native.candidate14
  Airbender.Compiler.HelperNative.MulDivCached.native.placement Airbender.Compiler.MemoryNative.MulDivCached.native.bank
  Airbender.Compiler.ConsumerNative.MulDivCached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.MulDivCached.native.candidate15
  Airbender.Compiler.HelperNative.MulDivCached.native.placement Airbender.Compiler.MemoryNative.MulDivCached.native.bank
  Airbender.Compiler.ConsumerNative.MulDivCached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.MulDivCached.native.candidate25
  Airbender.Compiler.HelperNative.MulDivCached.native.placement Airbender.Compiler.MemoryNative.MulDivCached.native.bank
  Airbender.Compiler.ConsumerNative.MulDivCached.native.typing)]

noncomputable def data : List NumericFunctionalBaseChecks.Data := (data0 ++ data4)

end Airbender.Compiler.HelperPayloadChecks.MulDivCached
