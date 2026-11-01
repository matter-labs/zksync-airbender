import Airbender.Proofs.GKRProtocol.MemoryFrameChecks.ShiftBinopCached.Bindings

namespace Airbender.Compiler.MemoryFrameChecks.ShiftBinopCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

theorem checked : NumericMemoryFrameChecks.check data = true := by decide +kernel

theorem originalChecked : Airbender.Compiler.MemoryFrameNative.ShiftBinopCached.native.ramFields.all (fun field =>
    field.baseFrameCheck Airbender.Compiler.MemoryNative.ShiftBinopCached.native.sourcePlacement Airbender.Compiler.MemoryNative.ShiftBinopCached.native.bank Airbender.Compiler.MemoryFrameNative.ShiftBinopCached.native.activeCoordinates Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.inputBank Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.bank) = true ∧
  Airbender.Compiler.MemoryFrameNative.ShiftBinopCached.native.initializationFields.all (fun field =>
    field.baseFrameCheck Airbender.Compiler.MemoryNative.ShiftBinopCached.native.sourcePlacement Airbender.Compiler.MemoryNative.ShiftBinopCached.native.bank Airbender.Compiler.MemoryFrameNative.ShiftBinopCached.native.allCoordinates Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.inputBank Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.bank) = true ∧
  Airbender.Compiler.MemoryFrameNative.ShiftBinopCached.native.executeFields.all (fun field =>
    field.baseFrameCheck Airbender.Compiler.MemoryNative.ShiftBinopCached.native.sourcePlacement Airbender.Compiler.MemoryNative.ShiftBinopCached.native.bank Airbender.Compiler.MemoryFrameNative.ShiftBinopCached.native.allCoordinates Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.inputBank Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.bank) = true :=
  NumericMemoryFrameChecks.check_sound data Airbender.Compiler.MemoryFrameNative.ShiftBinopCached.native.ramFields Airbender.Compiler.MemoryFrameNative.ShiftBinopCached.native.initializationFields Airbender.Compiler.MemoryFrameNative.ShiftBinopCached.native.executeFields
    Airbender.Compiler.MemoryNative.ShiftBinopCached.native.sourcePlacement Airbender.Compiler.MemoryNative.ShiftBinopCached.native.bank Airbender.Compiler.MemoryFrameNative.ShiftBinopCached.native.activeCoordinates Airbender.Compiler.MemoryFrameNative.ShiftBinopCached.native.allCoordinates
    Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.inputBank Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.bank active_binding all_binding placement_binding nativeAddress_binding inputAddress_binding fullAddress_binding ram_binding initialization_binding execution_binding checked

end Airbender.Compiler.MemoryFrameChecks.ShiftBinopCached
