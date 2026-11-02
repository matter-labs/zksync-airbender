import Airbender.Proofs.GKRProtocol.HelperPayloadChecks.JumpBranchUncached.Inputs
import Airbender.Proofs.GKRProtocol.NumericNativePayloadChecks

namespace Airbender.Compiler.HelperPayloadChecks.JumpBranchUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def originalEntries := [
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.JumpBranchUncached.native.candidate4
  Airbender.Compiler.HelperNative.JumpBranchUncached.native.placement Airbender.Compiler.MemoryNative.JumpBranchUncached.native.bank
  Airbender.Compiler.ConsumerNative.JumpBranchUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.JumpBranchUncached.native.candidate6
  Airbender.Compiler.HelperNative.JumpBranchUncached.native.placement Airbender.Compiler.MemoryNative.JumpBranchUncached.native.bank
  Airbender.Compiler.ConsumerNative.JumpBranchUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.JumpBranchUncached.native.candidate7
  Airbender.Compiler.HelperNative.JumpBranchUncached.native.placement Airbender.Compiler.MemoryNative.JumpBranchUncached.native.bank
  Airbender.Compiler.ConsumerNative.JumpBranchUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.JumpBranchUncached.native.candidate8
  Airbender.Compiler.HelperNative.JumpBranchUncached.native.placement Airbender.Compiler.MemoryNative.JumpBranchUncached.native.bank
  Airbender.Compiler.ConsumerNative.JumpBranchUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.JumpBranchUncached.native.candidate9
  Airbender.Compiler.HelperNative.JumpBranchUncached.native.placement Airbender.Compiler.MemoryNative.JumpBranchUncached.native.bank
  Airbender.Compiler.ConsumerNative.JumpBranchUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.JumpBranchUncached.native.candidate10
  Airbender.Compiler.HelperNative.JumpBranchUncached.native.placement Airbender.Compiler.MemoryNative.JumpBranchUncached.native.bank
  Airbender.Compiler.ConsumerNative.JumpBranchUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.JumpBranchUncached.native.candidate11
  Airbender.Compiler.HelperNative.JumpBranchUncached.native.placement Airbender.Compiler.MemoryNative.JumpBranchUncached.native.bank
  Airbender.Compiler.ConsumerNative.JumpBranchUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.JumpBranchUncached.native.candidate19
  Airbender.Compiler.HelperNative.JumpBranchUncached.native.placement Airbender.Compiler.MemoryNative.JumpBranchUncached.native.bank
  Airbender.Compiler.ConsumerNative.JumpBranchUncached.native.typing]

end Airbender.Compiler.HelperPayloadChecks.JumpBranchUncached
