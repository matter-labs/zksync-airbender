import Airbender.Proofs.GKRProtocol.MemoryFrameChecks.UnifiedCached.Bindings

namespace Airbender.Compiler.MemoryFrameChecks.UnifiedCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

theorem checked : NumericMemoryFrameChecks.check data = true := by decide +kernel

theorem originalChecked : Airbender.Compiler.MemoryFrameNative.UnifiedCached.native.ramFields.all (fun field =>
    field.baseFrameCheck Airbender.Compiler.MemoryNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.MemoryFrameNative.UnifiedCached.native.activeCoordinates Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.inputBank Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank) = true ∧
  Airbender.Compiler.MemoryFrameNative.UnifiedCached.native.initializationFields.all (fun field =>
    field.baseFrameCheck Airbender.Compiler.MemoryNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.MemoryFrameNative.UnifiedCached.native.allCoordinates Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.inputBank Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank) = true ∧
  Airbender.Compiler.MemoryFrameNative.UnifiedCached.native.executeFields.all (fun field =>
    field.baseFrameCheck Airbender.Compiler.MemoryNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.MemoryFrameNative.UnifiedCached.native.allCoordinates Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.inputBank Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank) = true :=
  NumericMemoryFrameChecks.check_sound data Airbender.Compiler.MemoryFrameNative.UnifiedCached.native.ramFields Airbender.Compiler.MemoryFrameNative.UnifiedCached.native.initializationFields Airbender.Compiler.MemoryFrameNative.UnifiedCached.native.executeFields
    Airbender.Compiler.MemoryNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.MemoryFrameNative.UnifiedCached.native.activeCoordinates Airbender.Compiler.MemoryFrameNative.UnifiedCached.native.allCoordinates
    Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.inputBank Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank active_binding all_binding placement_binding nativeAddress_binding inputAddress_binding fullAddress_binding ram_binding initialization_binding execution_binding checked

end Airbender.Compiler.MemoryFrameChecks.UnifiedCached
