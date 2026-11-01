import Airbender.Proofs.GKRProtocol.MemoryFrameChecks.JumpBranchUncached.Bindings

namespace Airbender.Compiler.MemoryFrameChecks.JumpBranchUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

theorem checked : NumericMemoryFrameChecks.check data = true := by decide +kernel

theorem originalChecked : Airbender.Compiler.MemoryFrameNative.JumpBranchUncached.native.ramFields.all (fun field =>
    field.baseFrameCheck Airbender.Compiler.MemoryNative.JumpBranchUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.JumpBranchUncached.native.bank Airbender.Compiler.MemoryFrameNative.JumpBranchUncached.native.activeCoordinates Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.inputBank Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.bank) = true ∧
  Airbender.Compiler.MemoryFrameNative.JumpBranchUncached.native.initializationFields.all (fun field =>
    field.baseFrameCheck Airbender.Compiler.MemoryNative.JumpBranchUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.JumpBranchUncached.native.bank Airbender.Compiler.MemoryFrameNative.JumpBranchUncached.native.allCoordinates Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.inputBank Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.bank) = true ∧
  Airbender.Compiler.MemoryFrameNative.JumpBranchUncached.native.executeFields.all (fun field =>
    field.baseFrameCheck Airbender.Compiler.MemoryNative.JumpBranchUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.JumpBranchUncached.native.bank Airbender.Compiler.MemoryFrameNative.JumpBranchUncached.native.allCoordinates Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.inputBank Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.bank) = true :=
  NumericMemoryFrameChecks.check_sound data Airbender.Compiler.MemoryFrameNative.JumpBranchUncached.native.ramFields Airbender.Compiler.MemoryFrameNative.JumpBranchUncached.native.initializationFields Airbender.Compiler.MemoryFrameNative.JumpBranchUncached.native.executeFields
    Airbender.Compiler.MemoryNative.JumpBranchUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.JumpBranchUncached.native.bank Airbender.Compiler.MemoryFrameNative.JumpBranchUncached.native.activeCoordinates Airbender.Compiler.MemoryFrameNative.JumpBranchUncached.native.allCoordinates
    Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.inputBank Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.bank active_binding all_binding placement_binding nativeAddress_binding inputAddress_binding fullAddress_binding ram_binding initialization_binding execution_binding checked

end Airbender.Compiler.MemoryFrameChecks.JumpBranchUncached
