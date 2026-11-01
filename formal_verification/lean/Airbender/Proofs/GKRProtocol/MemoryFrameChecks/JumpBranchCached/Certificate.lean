import Airbender.Proofs.GKRProtocol.MemoryFrameChecks.JumpBranchCached.Bindings

namespace Airbender.Compiler.MemoryFrameChecks.JumpBranchCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

theorem checked : NumericMemoryFrameChecks.check data = true := by decide +kernel

theorem originalChecked : Airbender.Compiler.MemoryFrameNative.JumpBranchCached.native.ramFields.all (fun field =>
    field.baseFrameCheck Airbender.Compiler.MemoryNative.JumpBranchCached.native.sourcePlacement Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank Airbender.Compiler.MemoryFrameNative.JumpBranchCached.native.activeCoordinates Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.inputBank Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.bank) = true ∧
  Airbender.Compiler.MemoryFrameNative.JumpBranchCached.native.initializationFields.all (fun field =>
    field.baseFrameCheck Airbender.Compiler.MemoryNative.JumpBranchCached.native.sourcePlacement Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank Airbender.Compiler.MemoryFrameNative.JumpBranchCached.native.allCoordinates Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.inputBank Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.bank) = true ∧
  Airbender.Compiler.MemoryFrameNative.JumpBranchCached.native.executeFields.all (fun field =>
    field.baseFrameCheck Airbender.Compiler.MemoryNative.JumpBranchCached.native.sourcePlacement Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank Airbender.Compiler.MemoryFrameNative.JumpBranchCached.native.allCoordinates Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.inputBank Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.bank) = true :=
  NumericMemoryFrameChecks.check_sound data Airbender.Compiler.MemoryFrameNative.JumpBranchCached.native.ramFields Airbender.Compiler.MemoryFrameNative.JumpBranchCached.native.initializationFields Airbender.Compiler.MemoryFrameNative.JumpBranchCached.native.executeFields
    Airbender.Compiler.MemoryNative.JumpBranchCached.native.sourcePlacement Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank Airbender.Compiler.MemoryFrameNative.JumpBranchCached.native.activeCoordinates Airbender.Compiler.MemoryFrameNative.JumpBranchCached.native.allCoordinates
    Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.inputBank Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.bank active_binding all_binding placement_binding nativeAddress_binding inputAddress_binding fullAddress_binding ram_binding initialization_binding execution_binding checked

end Airbender.Compiler.MemoryFrameChecks.JumpBranchCached
