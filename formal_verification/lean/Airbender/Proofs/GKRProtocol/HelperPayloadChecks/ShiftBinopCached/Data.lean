import Airbender.Proofs.GKRProtocol.HelperPayloadChecks.ShiftBinopCached.Typed
import Airbender.Import.GKRProtocol.NumericFunctionalBaseImport

namespace Airbender.Compiler.HelperPayloadChecks.ShiftBinopCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

numeric_functional_base_capture data0 := [
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.ShiftBinopCached.native.candidate2
  Airbender.Compiler.HelperNative.ShiftBinopCached.native.placement Airbender.Compiler.MemoryNative.ShiftBinopCached.native.bank
  Airbender.Compiler.ConsumerNative.ShiftBinopCached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.ShiftBinopCached.native.candidate4
  Airbender.Compiler.HelperNative.ShiftBinopCached.native.placement Airbender.Compiler.MemoryNative.ShiftBinopCached.native.bank
  Airbender.Compiler.ConsumerNative.ShiftBinopCached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.ShiftBinopCached.native.candidate5
  Airbender.Compiler.HelperNative.ShiftBinopCached.native.placement Airbender.Compiler.MemoryNative.ShiftBinopCached.native.bank
  Airbender.Compiler.ConsumerNative.ShiftBinopCached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.ShiftBinopCached.native.candidate6
  Airbender.Compiler.HelperNative.ShiftBinopCached.native.placement Airbender.Compiler.MemoryNative.ShiftBinopCached.native.bank
  Airbender.Compiler.ConsumerNative.ShiftBinopCached.native.typing)]

numeric_functional_base_capture data4 := [
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.ShiftBinopCached.native.candidate7
  Airbender.Compiler.HelperNative.ShiftBinopCached.native.placement Airbender.Compiler.MemoryNative.ShiftBinopCached.native.bank
  Airbender.Compiler.ConsumerNative.ShiftBinopCached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.ShiftBinopCached.native.candidate8
  Airbender.Compiler.HelperNative.ShiftBinopCached.native.placement Airbender.Compiler.MemoryNative.ShiftBinopCached.native.bank
  Airbender.Compiler.ConsumerNative.ShiftBinopCached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.ShiftBinopCached.native.candidate9
  Airbender.Compiler.HelperNative.ShiftBinopCached.native.placement Airbender.Compiler.MemoryNative.ShiftBinopCached.native.bank
  Airbender.Compiler.ConsumerNative.ShiftBinopCached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.ShiftBinopCached.native.candidate13
  Airbender.Compiler.HelperNative.ShiftBinopCached.native.placement Airbender.Compiler.MemoryNative.ShiftBinopCached.native.bank
  Airbender.Compiler.ConsumerNative.ShiftBinopCached.native.typing)]

noncomputable def data : List NumericFunctionalBaseChecks.Data := (data0 ++ data4)

end Airbender.Compiler.HelperPayloadChecks.ShiftBinopCached
