import Airbender.Proofs.GKRProtocol.MemoryFrameChecks.WordMemoryCached.Bindings

namespace Airbender.Compiler.MemoryFrameChecks.WordMemoryCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

theorem checked : NumericMemoryFrameChecks.check data = true := by decide +kernel

theorem originalChecked : Airbender.Compiler.MemoryFrameNative.WordMemoryCached.native.ramFields.all (fun field =>
    field.baseFrameCheck Airbender.Compiler.MemoryNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.MemoryNative.WordMemoryCached.native.bank Airbender.Compiler.MemoryFrameNative.WordMemoryCached.native.activeCoordinates Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.inputBank Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.bank) = true ∧
  Airbender.Compiler.MemoryFrameNative.WordMemoryCached.native.initializationFields.all (fun field =>
    field.baseFrameCheck Airbender.Compiler.MemoryNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.MemoryNative.WordMemoryCached.native.bank Airbender.Compiler.MemoryFrameNative.WordMemoryCached.native.allCoordinates Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.inputBank Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.bank) = true ∧
  Airbender.Compiler.MemoryFrameNative.WordMemoryCached.native.executeFields.all (fun field =>
    field.baseFrameCheck Airbender.Compiler.MemoryNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.MemoryNative.WordMemoryCached.native.bank Airbender.Compiler.MemoryFrameNative.WordMemoryCached.native.allCoordinates Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.inputBank Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.bank) = true :=
  NumericMemoryFrameChecks.check_sound data Airbender.Compiler.MemoryFrameNative.WordMemoryCached.native.ramFields Airbender.Compiler.MemoryFrameNative.WordMemoryCached.native.initializationFields Airbender.Compiler.MemoryFrameNative.WordMemoryCached.native.executeFields
    Airbender.Compiler.MemoryNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.MemoryNative.WordMemoryCached.native.bank Airbender.Compiler.MemoryFrameNative.WordMemoryCached.native.activeCoordinates Airbender.Compiler.MemoryFrameNative.WordMemoryCached.native.allCoordinates
    Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.inputBank Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.bank active_binding all_binding placement_binding nativeAddress_binding inputAddress_binding fullAddress_binding ram_binding initialization_binding execution_binding checked

end Airbender.Compiler.MemoryFrameChecks.WordMemoryCached
