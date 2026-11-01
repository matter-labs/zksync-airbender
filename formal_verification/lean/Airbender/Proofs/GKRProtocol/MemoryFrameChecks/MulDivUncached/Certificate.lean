import Airbender.Proofs.GKRProtocol.MemoryFrameChecks.MulDivUncached.Bindings

namespace Airbender.Compiler.MemoryFrameChecks.MulDivUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

theorem checked : NumericMemoryFrameChecks.check data = true := by decide +kernel

theorem originalChecked : Airbender.Compiler.MemoryFrameNative.MulDivUncached.native.ramFields.all (fun field =>
    field.baseFrameCheck Airbender.Compiler.MemoryNative.MulDivUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.MulDivUncached.native.bank Airbender.Compiler.MemoryFrameNative.MulDivUncached.native.activeCoordinates Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.inputBank Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.bank) = true ∧
  Airbender.Compiler.MemoryFrameNative.MulDivUncached.native.initializationFields.all (fun field =>
    field.baseFrameCheck Airbender.Compiler.MemoryNative.MulDivUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.MulDivUncached.native.bank Airbender.Compiler.MemoryFrameNative.MulDivUncached.native.allCoordinates Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.inputBank Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.bank) = true ∧
  Airbender.Compiler.MemoryFrameNative.MulDivUncached.native.executeFields.all (fun field =>
    field.baseFrameCheck Airbender.Compiler.MemoryNative.MulDivUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.MulDivUncached.native.bank Airbender.Compiler.MemoryFrameNative.MulDivUncached.native.allCoordinates Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.inputBank Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.bank) = true :=
  NumericMemoryFrameChecks.check_sound data Airbender.Compiler.MemoryFrameNative.MulDivUncached.native.ramFields Airbender.Compiler.MemoryFrameNative.MulDivUncached.native.initializationFields Airbender.Compiler.MemoryFrameNative.MulDivUncached.native.executeFields
    Airbender.Compiler.MemoryNative.MulDivUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.MulDivUncached.native.bank Airbender.Compiler.MemoryFrameNative.MulDivUncached.native.activeCoordinates Airbender.Compiler.MemoryFrameNative.MulDivUncached.native.allCoordinates
    Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.inputBank Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.bank active_binding all_binding placement_binding nativeAddress_binding inputAddress_binding fullAddress_binding ram_binding initialization_binding execution_binding checked

end Airbender.Compiler.MemoryFrameChecks.MulDivUncached
