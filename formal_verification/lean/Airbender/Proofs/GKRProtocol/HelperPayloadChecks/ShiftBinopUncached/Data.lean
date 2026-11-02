import Airbender.Proofs.GKRProtocol.HelperPayloadChecks.ShiftBinopUncached.Typed
import Airbender.Import.GKRProtocol.NumericFunctionalBaseImport

namespace Airbender.Compiler.HelperPayloadChecks.ShiftBinopUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

numeric_functional_base_capture data0 := [
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.ShiftBinopUncached.native.candidate2
  Airbender.Compiler.HelperNative.ShiftBinopUncached.native.placement Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.bank
  Airbender.Compiler.ConsumerNative.ShiftBinopUncached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.ShiftBinopUncached.native.candidate4
  Airbender.Compiler.HelperNative.ShiftBinopUncached.native.placement Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.bank
  Airbender.Compiler.ConsumerNative.ShiftBinopUncached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.ShiftBinopUncached.native.candidate5
  Airbender.Compiler.HelperNative.ShiftBinopUncached.native.placement Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.bank
  Airbender.Compiler.ConsumerNative.ShiftBinopUncached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.ShiftBinopUncached.native.candidate6
  Airbender.Compiler.HelperNative.ShiftBinopUncached.native.placement Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.bank
  Airbender.Compiler.ConsumerNative.ShiftBinopUncached.native.typing)]

numeric_functional_base_capture data4 := [
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.ShiftBinopUncached.native.candidate7
  Airbender.Compiler.HelperNative.ShiftBinopUncached.native.placement Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.bank
  Airbender.Compiler.ConsumerNative.ShiftBinopUncached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.ShiftBinopUncached.native.candidate8
  Airbender.Compiler.HelperNative.ShiftBinopUncached.native.placement Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.bank
  Airbender.Compiler.ConsumerNative.ShiftBinopUncached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.ShiftBinopUncached.native.candidate9
  Airbender.Compiler.HelperNative.ShiftBinopUncached.native.placement Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.bank
  Airbender.Compiler.ConsumerNative.ShiftBinopUncached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.ShiftBinopUncached.native.candidate13
  Airbender.Compiler.HelperNative.ShiftBinopUncached.native.placement Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.bank
  Airbender.Compiler.ConsumerNative.ShiftBinopUncached.native.typing)]

noncomputable def data : List NumericFunctionalBaseChecks.Data := (data0 ++ data4)

end Airbender.Compiler.HelperPayloadChecks.ShiftBinopUncached
