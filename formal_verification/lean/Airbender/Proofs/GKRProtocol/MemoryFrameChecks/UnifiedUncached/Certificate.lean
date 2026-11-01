import Airbender.Proofs.GKRProtocol.MemoryFrameChecks.UnifiedUncached.Bindings

namespace Airbender.Compiler.MemoryFrameChecks.UnifiedUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

theorem checked : NumericMemoryFrameChecks.check data = true := by decide +kernel

theorem originalChecked : Airbender.Compiler.MemoryFrameNative.UnifiedUncached.native.ramFields.all (fun field =>
    field.baseFrameCheck Airbender.Compiler.MemoryNative.UnifiedUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank Airbender.Compiler.MemoryFrameNative.UnifiedUncached.native.activeCoordinates Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.inputBank Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.bank) = true ∧
  Airbender.Compiler.MemoryFrameNative.UnifiedUncached.native.initializationFields.all (fun field =>
    field.baseFrameCheck Airbender.Compiler.MemoryNative.UnifiedUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank Airbender.Compiler.MemoryFrameNative.UnifiedUncached.native.allCoordinates Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.inputBank Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.bank) = true ∧
  Airbender.Compiler.MemoryFrameNative.UnifiedUncached.native.executeFields.all (fun field =>
    field.baseFrameCheck Airbender.Compiler.MemoryNative.UnifiedUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank Airbender.Compiler.MemoryFrameNative.UnifiedUncached.native.allCoordinates Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.inputBank Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.bank) = true :=
  NumericMemoryFrameChecks.check_sound data Airbender.Compiler.MemoryFrameNative.UnifiedUncached.native.ramFields Airbender.Compiler.MemoryFrameNative.UnifiedUncached.native.initializationFields Airbender.Compiler.MemoryFrameNative.UnifiedUncached.native.executeFields
    Airbender.Compiler.MemoryNative.UnifiedUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank Airbender.Compiler.MemoryFrameNative.UnifiedUncached.native.activeCoordinates Airbender.Compiler.MemoryFrameNative.UnifiedUncached.native.allCoordinates
    Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.inputBank Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.bank active_binding all_binding placement_binding nativeAddress_binding inputAddress_binding fullAddress_binding ram_binding initialization_binding execution_binding checked

end Airbender.Compiler.MemoryFrameChecks.UnifiedUncached
