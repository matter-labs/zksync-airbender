import Airbender.Proofs.GKRProtocol.MemoryFrameChecks.BigintCached.Bindings

namespace Airbender.Compiler.MemoryFrameChecks.BigintCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

theorem checked : NumericMemoryFrameChecks.check data = true := by decide +kernel

theorem originalChecked : Airbender.Compiler.MemoryFrameNative.BigintCached.native.ramFields.all (fun field =>
    field.baseFrameCheck Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryFrameNative.BigintCached.native.activeCoordinates Airbender.Compiler.FullArithmeticNative.BigintCached.native.inputBank Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank) = true ∧
  Airbender.Compiler.MemoryFrameNative.BigintCached.native.initializationFields.all (fun field =>
    field.baseFrameCheck Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryFrameNative.BigintCached.native.allCoordinates Airbender.Compiler.FullArithmeticNative.BigintCached.native.inputBank Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank) = true ∧
  Airbender.Compiler.MemoryFrameNative.BigintCached.native.executeFields.all (fun field =>
    field.baseFrameCheck Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryFrameNative.BigintCached.native.allCoordinates Airbender.Compiler.FullArithmeticNative.BigintCached.native.inputBank Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank) = true :=
  NumericMemoryFrameChecks.check_sound data Airbender.Compiler.MemoryFrameNative.BigintCached.native.ramFields Airbender.Compiler.MemoryFrameNative.BigintCached.native.initializationFields Airbender.Compiler.MemoryFrameNative.BigintCached.native.executeFields
    Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryFrameNative.BigintCached.native.activeCoordinates Airbender.Compiler.MemoryFrameNative.BigintCached.native.allCoordinates
    Airbender.Compiler.FullArithmeticNative.BigintCached.native.inputBank Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank active_binding all_binding placement_binding nativeAddress_binding inputAddress_binding fullAddress_binding ram_binding initialization_binding execution_binding checked

end Airbender.Compiler.MemoryFrameChecks.BigintCached
