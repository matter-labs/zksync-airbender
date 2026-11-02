import Airbender.Proofs.GKRProtocol.HelperPayloadChecks.JumpBranchUncached.Typed
import Airbender.Import.GKRProtocol.NumericFunctionalBaseImport

namespace Airbender.Compiler.HelperPayloadChecks.JumpBranchUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

numeric_functional_base_capture data0 := [
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.JumpBranchUncached.native.candidate4
  Airbender.Compiler.HelperNative.JumpBranchUncached.native.placement Airbender.Compiler.MemoryNative.JumpBranchUncached.native.bank
  Airbender.Compiler.ConsumerNative.JumpBranchUncached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.JumpBranchUncached.native.candidate6
  Airbender.Compiler.HelperNative.JumpBranchUncached.native.placement Airbender.Compiler.MemoryNative.JumpBranchUncached.native.bank
  Airbender.Compiler.ConsumerNative.JumpBranchUncached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.JumpBranchUncached.native.candidate7
  Airbender.Compiler.HelperNative.JumpBranchUncached.native.placement Airbender.Compiler.MemoryNative.JumpBranchUncached.native.bank
  Airbender.Compiler.ConsumerNative.JumpBranchUncached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.JumpBranchUncached.native.candidate8
  Airbender.Compiler.HelperNative.JumpBranchUncached.native.placement Airbender.Compiler.MemoryNative.JumpBranchUncached.native.bank
  Airbender.Compiler.ConsumerNative.JumpBranchUncached.native.typing)]

numeric_functional_base_capture data4 := [
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.JumpBranchUncached.native.candidate9
  Airbender.Compiler.HelperNative.JumpBranchUncached.native.placement Airbender.Compiler.MemoryNative.JumpBranchUncached.native.bank
  Airbender.Compiler.ConsumerNative.JumpBranchUncached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.JumpBranchUncached.native.candidate10
  Airbender.Compiler.HelperNative.JumpBranchUncached.native.placement Airbender.Compiler.MemoryNative.JumpBranchUncached.native.bank
  Airbender.Compiler.ConsumerNative.JumpBranchUncached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.JumpBranchUncached.native.candidate11
  Airbender.Compiler.HelperNative.JumpBranchUncached.native.placement Airbender.Compiler.MemoryNative.JumpBranchUncached.native.bank
  Airbender.Compiler.ConsumerNative.JumpBranchUncached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.JumpBranchUncached.native.candidate19
  Airbender.Compiler.HelperNative.JumpBranchUncached.native.placement Airbender.Compiler.MemoryNative.JumpBranchUncached.native.bank
  Airbender.Compiler.ConsumerNative.JumpBranchUncached.native.typing)]

noncomputable def data : List NumericFunctionalBaseChecks.Data := (data0 ++ data4)

end Airbender.Compiler.HelperPayloadChecks.JumpBranchUncached
