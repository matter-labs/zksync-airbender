import Airbender.Proofs.GKRProtocol.MemoryFrameChecks.MulDivCached.Bindings

namespace Airbender.Compiler.MemoryFrameChecks.MulDivCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

theorem checked : NumericMemoryFrameChecks.check data = true := by decide +kernel

theorem originalChecked : Airbender.Compiler.MemoryFrameNative.MulDivCached.native.ramFields.all (fun field =>
    field.baseFrameCheck Airbender.Compiler.MemoryNative.MulDivCached.native.sourcePlacement Airbender.Compiler.MemoryNative.MulDivCached.native.bank Airbender.Compiler.MemoryFrameNative.MulDivCached.native.activeCoordinates Airbender.Compiler.FullArithmeticNative.MulDivCached.native.inputBank Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank) = true ∧
  Airbender.Compiler.MemoryFrameNative.MulDivCached.native.initializationFields.all (fun field =>
    field.baseFrameCheck Airbender.Compiler.MemoryNative.MulDivCached.native.sourcePlacement Airbender.Compiler.MemoryNative.MulDivCached.native.bank Airbender.Compiler.MemoryFrameNative.MulDivCached.native.allCoordinates Airbender.Compiler.FullArithmeticNative.MulDivCached.native.inputBank Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank) = true ∧
  Airbender.Compiler.MemoryFrameNative.MulDivCached.native.executeFields.all (fun field =>
    field.baseFrameCheck Airbender.Compiler.MemoryNative.MulDivCached.native.sourcePlacement Airbender.Compiler.MemoryNative.MulDivCached.native.bank Airbender.Compiler.MemoryFrameNative.MulDivCached.native.allCoordinates Airbender.Compiler.FullArithmeticNative.MulDivCached.native.inputBank Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank) = true :=
  NumericMemoryFrameChecks.check_sound data Airbender.Compiler.MemoryFrameNative.MulDivCached.native.ramFields Airbender.Compiler.MemoryFrameNative.MulDivCached.native.initializationFields Airbender.Compiler.MemoryFrameNative.MulDivCached.native.executeFields
    Airbender.Compiler.MemoryNative.MulDivCached.native.sourcePlacement Airbender.Compiler.MemoryNative.MulDivCached.native.bank Airbender.Compiler.MemoryFrameNative.MulDivCached.native.activeCoordinates Airbender.Compiler.MemoryFrameNative.MulDivCached.native.allCoordinates
    Airbender.Compiler.FullArithmeticNative.MulDivCached.native.inputBank Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank active_binding all_binding placement_binding nativeAddress_binding inputAddress_binding fullAddress_binding ram_binding initialization_binding execution_binding checked

end Airbender.Compiler.MemoryFrameChecks.MulDivCached
