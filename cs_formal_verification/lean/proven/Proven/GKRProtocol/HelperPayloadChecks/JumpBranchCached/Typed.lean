module
import all Mathlib.Data.List.Sort
public import Proven.GKRProtocol.HelperPayloadChecks.JumpBranchCached.Inputs
public import Proven.GKRProtocol.NumericNativePayloadChecks

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.HelperPayloadChecks.JumpBranchCached
open Airbender Airbender.Compiler
set_option maxRecDepth 8192

noncomputable def originalEntries := [
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.JumpBranchCached.native.candidate4
  Airbender.Compiler.HelperNative.JumpBranchCached.native.placement Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank
  Airbender.Compiler.ConsumerNative.JumpBranchCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.JumpBranchCached.native.candidate6
  Airbender.Compiler.HelperNative.JumpBranchCached.native.placement Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank
  Airbender.Compiler.ConsumerNative.JumpBranchCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.JumpBranchCached.native.candidate7
  Airbender.Compiler.HelperNative.JumpBranchCached.native.placement Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank
  Airbender.Compiler.ConsumerNative.JumpBranchCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.JumpBranchCached.native.candidate8
  Airbender.Compiler.HelperNative.JumpBranchCached.native.placement Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank
  Airbender.Compiler.ConsumerNative.JumpBranchCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.JumpBranchCached.native.candidate9
  Airbender.Compiler.HelperNative.JumpBranchCached.native.placement Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank
  Airbender.Compiler.ConsumerNative.JumpBranchCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.JumpBranchCached.native.candidate10
  Airbender.Compiler.HelperNative.JumpBranchCached.native.placement Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank
  Airbender.Compiler.ConsumerNative.JumpBranchCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.JumpBranchCached.native.candidate11
  Airbender.Compiler.HelperNative.JumpBranchCached.native.placement Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank
  Airbender.Compiler.ConsumerNative.JumpBranchCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.JumpBranchCached.native.candidate19
  Airbender.Compiler.HelperNative.JumpBranchCached.native.placement Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank
  Airbender.Compiler.ConsumerNative.JumpBranchCached.native.typing]

end Airbender.Compiler.HelperPayloadChecks.JumpBranchCached
