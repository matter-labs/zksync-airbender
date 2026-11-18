module
import all Mathlib.Data.List.Sort
public import Proven.GKRProtocol.HelperPayloadChecks.JumpBranchCached.Typed
public import Proven.Import.GKRProtocol.NumericFunctionalBaseImport

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.HelperPayloadChecks.JumpBranchCached
open Airbender Airbender.Compiler
set_option maxRecDepth 8192

numeric_functional_base_capture data0 := [
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.JumpBranchCached.native.candidate4
  Airbender.Compiler.HelperNative.JumpBranchCached.native.placement Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank
  Airbender.Compiler.ConsumerNative.JumpBranchCached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.JumpBranchCached.native.candidate6
  Airbender.Compiler.HelperNative.JumpBranchCached.native.placement Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank
  Airbender.Compiler.ConsumerNative.JumpBranchCached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.JumpBranchCached.native.candidate7
  Airbender.Compiler.HelperNative.JumpBranchCached.native.placement Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank
  Airbender.Compiler.ConsumerNative.JumpBranchCached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.JumpBranchCached.native.candidate8
  Airbender.Compiler.HelperNative.JumpBranchCached.native.placement Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank
  Airbender.Compiler.ConsumerNative.JumpBranchCached.native.typing)]

numeric_functional_base_capture data4 := [
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.JumpBranchCached.native.candidate9
  Airbender.Compiler.HelperNative.JumpBranchCached.native.placement Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank
  Airbender.Compiler.ConsumerNative.JumpBranchCached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.JumpBranchCached.native.candidate10
  Airbender.Compiler.HelperNative.JumpBranchCached.native.placement Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank
  Airbender.Compiler.ConsumerNative.JumpBranchCached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.JumpBranchCached.native.candidate11
  Airbender.Compiler.HelperNative.JumpBranchCached.native.placement Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank
  Airbender.Compiler.ConsumerNative.JumpBranchCached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.JumpBranchCached.native.candidate19
  Airbender.Compiler.HelperNative.JumpBranchCached.native.placement Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank
  Airbender.Compiler.ConsumerNative.JumpBranchCached.native.typing)]

noncomputable def data : List NumericFunctionalBaseChecks.Data := (data0 ++ data4)

end Airbender.Compiler.HelperPayloadChecks.JumpBranchCached
