import Airbender.Proofs.GKRProtocol.MemoryFrameChecks.WordMemoryUncached.Bindings

namespace Airbender.Compiler.MemoryFrameChecks.WordMemoryUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

theorem checked : NumericMemoryFrameChecks.check data = true := by decide +kernel

theorem originalChecked : Airbender.Compiler.MemoryFrameNative.WordMemoryUncached.native.ramFields.all (fun field =>
    field.baseFrameCheck Airbender.Compiler.MemoryNative.WordMemoryUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank Airbender.Compiler.MemoryFrameNative.WordMemoryUncached.native.activeCoordinates Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.inputBank Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.bank) = true ∧
  Airbender.Compiler.MemoryFrameNative.WordMemoryUncached.native.initializationFields.all (fun field =>
    field.baseFrameCheck Airbender.Compiler.MemoryNative.WordMemoryUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank Airbender.Compiler.MemoryFrameNative.WordMemoryUncached.native.allCoordinates Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.inputBank Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.bank) = true ∧
  Airbender.Compiler.MemoryFrameNative.WordMemoryUncached.native.executeFields.all (fun field =>
    field.baseFrameCheck Airbender.Compiler.MemoryNative.WordMemoryUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank Airbender.Compiler.MemoryFrameNative.WordMemoryUncached.native.allCoordinates Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.inputBank Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.bank) = true :=
  NumericMemoryFrameChecks.check_sound data Airbender.Compiler.MemoryFrameNative.WordMemoryUncached.native.ramFields Airbender.Compiler.MemoryFrameNative.WordMemoryUncached.native.initializationFields Airbender.Compiler.MemoryFrameNative.WordMemoryUncached.native.executeFields
    Airbender.Compiler.MemoryNative.WordMemoryUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank Airbender.Compiler.MemoryFrameNative.WordMemoryUncached.native.activeCoordinates Airbender.Compiler.MemoryFrameNative.WordMemoryUncached.native.allCoordinates
    Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.inputBank Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.bank active_binding all_binding placement_binding nativeAddress_binding inputAddress_binding fullAddress_binding ram_binding initialization_binding execution_binding checked

end Airbender.Compiler.MemoryFrameChecks.WordMemoryUncached
