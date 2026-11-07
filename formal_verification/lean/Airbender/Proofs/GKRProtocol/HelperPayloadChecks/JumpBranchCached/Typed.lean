import Airbender.Proofs.GKRProtocol.HelperPayloadChecks.JumpBranchCached.Inputs
import Airbender.Proofs.GKRProtocol.NumericNativePayloadChecks

namespace Airbender.Compiler.HelperPayloadChecks.JumpBranchCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
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
