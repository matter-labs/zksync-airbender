import Airbender.Proofs.GKRProtocol.MemoryFrameChecks.SubwordMemoryCached.Bindings

namespace Airbender.Compiler.MemoryFrameChecks.SubwordMemoryCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

theorem checked : NumericMemoryFrameChecks.check data = true := by decide +kernel

theorem originalChecked : Airbender.Compiler.MemoryFrameNative.SubwordMemoryCached.native.ramFields.all (fun field =>
    field.baseFrameCheck Airbender.Compiler.MemoryNative.SubwordMemoryCached.native.sourcePlacement Airbender.Compiler.MemoryNative.SubwordMemoryCached.native.bank Airbender.Compiler.MemoryFrameNative.SubwordMemoryCached.native.activeCoordinates Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.inputBank Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.bank) = true ∧
  Airbender.Compiler.MemoryFrameNative.SubwordMemoryCached.native.initializationFields.all (fun field =>
    field.baseFrameCheck Airbender.Compiler.MemoryNative.SubwordMemoryCached.native.sourcePlacement Airbender.Compiler.MemoryNative.SubwordMemoryCached.native.bank Airbender.Compiler.MemoryFrameNative.SubwordMemoryCached.native.allCoordinates Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.inputBank Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.bank) = true ∧
  Airbender.Compiler.MemoryFrameNative.SubwordMemoryCached.native.executeFields.all (fun field =>
    field.baseFrameCheck Airbender.Compiler.MemoryNative.SubwordMemoryCached.native.sourcePlacement Airbender.Compiler.MemoryNative.SubwordMemoryCached.native.bank Airbender.Compiler.MemoryFrameNative.SubwordMemoryCached.native.allCoordinates Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.inputBank Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.bank) = true :=
  NumericMemoryFrameChecks.check_sound data Airbender.Compiler.MemoryFrameNative.SubwordMemoryCached.native.ramFields Airbender.Compiler.MemoryFrameNative.SubwordMemoryCached.native.initializationFields Airbender.Compiler.MemoryFrameNative.SubwordMemoryCached.native.executeFields
    Airbender.Compiler.MemoryNative.SubwordMemoryCached.native.sourcePlacement Airbender.Compiler.MemoryNative.SubwordMemoryCached.native.bank Airbender.Compiler.MemoryFrameNative.SubwordMemoryCached.native.activeCoordinates Airbender.Compiler.MemoryFrameNative.SubwordMemoryCached.native.allCoordinates
    Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.inputBank Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.bank active_binding all_binding placement_binding nativeAddress_binding inputAddress_binding fullAddress_binding ram_binding initialization_binding execution_binding checked

end Airbender.Compiler.MemoryFrameChecks.SubwordMemoryCached
