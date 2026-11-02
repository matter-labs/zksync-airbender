import Airbender.Proofs.GKRProtocol.HelperPayloadChecks.MulDivUncached.Typed
import Airbender.Import.GKRProtocol.NumericFunctionalBaseImport

namespace Airbender.Compiler.HelperPayloadChecks.MulDivUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

numeric_functional_base_capture data0 := [
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.MulDivUncached.native.candidate8
  Airbender.Compiler.HelperNative.MulDivUncached.native.placement Airbender.Compiler.MemoryNative.MulDivUncached.native.bank
  Airbender.Compiler.ConsumerNative.MulDivUncached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.MulDivUncached.native.candidate10
  Airbender.Compiler.HelperNative.MulDivUncached.native.placement Airbender.Compiler.MemoryNative.MulDivUncached.native.bank
  Airbender.Compiler.ConsumerNative.MulDivUncached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.MulDivUncached.native.candidate11
  Airbender.Compiler.HelperNative.MulDivUncached.native.placement Airbender.Compiler.MemoryNative.MulDivUncached.native.bank
  Airbender.Compiler.ConsumerNative.MulDivUncached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.MulDivUncached.native.candidate12
  Airbender.Compiler.HelperNative.MulDivUncached.native.placement Airbender.Compiler.MemoryNative.MulDivUncached.native.bank
  Airbender.Compiler.ConsumerNative.MulDivUncached.native.typing)]

numeric_functional_base_capture data4 := [
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.MulDivUncached.native.candidate13
  Airbender.Compiler.HelperNative.MulDivUncached.native.placement Airbender.Compiler.MemoryNative.MulDivUncached.native.bank
  Airbender.Compiler.ConsumerNative.MulDivUncached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.MulDivUncached.native.candidate14
  Airbender.Compiler.HelperNative.MulDivUncached.native.placement Airbender.Compiler.MemoryNative.MulDivUncached.native.bank
  Airbender.Compiler.ConsumerNative.MulDivUncached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.MulDivUncached.native.candidate15
  Airbender.Compiler.HelperNative.MulDivUncached.native.placement Airbender.Compiler.MemoryNative.MulDivUncached.native.bank
  Airbender.Compiler.ConsumerNative.MulDivUncached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.MulDivUncached.native.candidate25
  Airbender.Compiler.HelperNative.MulDivUncached.native.placement Airbender.Compiler.MemoryNative.MulDivUncached.native.bank
  Airbender.Compiler.ConsumerNative.MulDivUncached.native.typing)]

noncomputable def data : List NumericFunctionalBaseChecks.Data := (data0 ++ data4)

end Airbender.Compiler.HelperPayloadChecks.MulDivUncached
