import Airbender.Proofs.GKRProtocol.MemoryFrameChecks.BigintUncached.Bindings

namespace Airbender.Compiler.MemoryFrameChecks.BigintUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

theorem checked : NumericMemoryFrameChecks.check data = true := by decide +kernel

theorem originalChecked : Airbender.Compiler.MemoryFrameNative.BigintUncached.native.ramFields.all (fun field =>
    field.baseFrameCheck Airbender.Compiler.MemoryNative.BigintUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintUncached.native.bank Airbender.Compiler.MemoryFrameNative.BigintUncached.native.activeCoordinates Airbender.Compiler.FullArithmeticNative.BigintUncached.native.inputBank Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank) = true ∧
  Airbender.Compiler.MemoryFrameNative.BigintUncached.native.initializationFields.all (fun field =>
    field.baseFrameCheck Airbender.Compiler.MemoryNative.BigintUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintUncached.native.bank Airbender.Compiler.MemoryFrameNative.BigintUncached.native.allCoordinates Airbender.Compiler.FullArithmeticNative.BigintUncached.native.inputBank Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank) = true ∧
  Airbender.Compiler.MemoryFrameNative.BigintUncached.native.executeFields.all (fun field =>
    field.baseFrameCheck Airbender.Compiler.MemoryNative.BigintUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintUncached.native.bank Airbender.Compiler.MemoryFrameNative.BigintUncached.native.allCoordinates Airbender.Compiler.FullArithmeticNative.BigintUncached.native.inputBank Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank) = true :=
  NumericMemoryFrameChecks.check_sound data Airbender.Compiler.MemoryFrameNative.BigintUncached.native.ramFields Airbender.Compiler.MemoryFrameNative.BigintUncached.native.initializationFields Airbender.Compiler.MemoryFrameNative.BigintUncached.native.executeFields
    Airbender.Compiler.MemoryNative.BigintUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintUncached.native.bank Airbender.Compiler.MemoryFrameNative.BigintUncached.native.activeCoordinates Airbender.Compiler.MemoryFrameNative.BigintUncached.native.allCoordinates
    Airbender.Compiler.FullArithmeticNative.BigintUncached.native.inputBank Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank active_binding all_binding placement_binding nativeAddress_binding inputAddress_binding fullAddress_binding ram_binding initialization_binding execution_binding checked

end Airbender.Compiler.MemoryFrameChecks.BigintUncached
