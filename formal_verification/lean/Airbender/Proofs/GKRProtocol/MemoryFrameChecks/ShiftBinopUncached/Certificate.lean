import Airbender.Proofs.GKRProtocol.MemoryFrameChecks.ShiftBinopUncached.Bindings

namespace Airbender.Compiler.MemoryFrameChecks.ShiftBinopUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

theorem checked : NumericMemoryFrameChecks.check data = true := by decide +kernel

theorem originalChecked : Airbender.Compiler.MemoryFrameNative.ShiftBinopUncached.native.ramFields.all (fun field =>
    field.baseFrameCheck Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.bank Airbender.Compiler.MemoryFrameNative.ShiftBinopUncached.native.activeCoordinates Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.inputBank Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank) = true ∧
  Airbender.Compiler.MemoryFrameNative.ShiftBinopUncached.native.initializationFields.all (fun field =>
    field.baseFrameCheck Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.bank Airbender.Compiler.MemoryFrameNative.ShiftBinopUncached.native.allCoordinates Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.inputBank Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank) = true ∧
  Airbender.Compiler.MemoryFrameNative.ShiftBinopUncached.native.executeFields.all (fun field =>
    field.baseFrameCheck Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.bank Airbender.Compiler.MemoryFrameNative.ShiftBinopUncached.native.allCoordinates Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.inputBank Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank) = true :=
  NumericMemoryFrameChecks.check_sound data Airbender.Compiler.MemoryFrameNative.ShiftBinopUncached.native.ramFields Airbender.Compiler.MemoryFrameNative.ShiftBinopUncached.native.initializationFields Airbender.Compiler.MemoryFrameNative.ShiftBinopUncached.native.executeFields
    Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.bank Airbender.Compiler.MemoryFrameNative.ShiftBinopUncached.native.activeCoordinates Airbender.Compiler.MemoryFrameNative.ShiftBinopUncached.native.allCoordinates
    Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.inputBank Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank active_binding all_binding placement_binding nativeAddress_binding inputAddress_binding fullAddress_binding ram_binding initialization_binding execution_binding checked

end Airbender.Compiler.MemoryFrameChecks.ShiftBinopUncached
