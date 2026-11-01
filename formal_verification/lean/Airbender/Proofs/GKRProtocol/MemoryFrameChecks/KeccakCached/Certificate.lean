import Airbender.Proofs.GKRProtocol.MemoryFrameChecks.KeccakCached.Bindings

namespace Airbender.Compiler.MemoryFrameChecks.KeccakCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

theorem checked : NumericMemoryFrameChecks.check data = true := by decide +kernel

theorem originalChecked : Airbender.Compiler.MemoryFrameNative.KeccakCached.native.ramFields.all (fun field =>
    field.baseFrameCheck Airbender.Compiler.MemoryNative.KeccakCached.native.sourcePlacement Airbender.Compiler.MemoryNative.KeccakCached.native.bank Airbender.Compiler.MemoryFrameNative.KeccakCached.native.activeCoordinates Airbender.Compiler.FullArithmeticNative.KeccakCached.native.inputBank Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank) = true ∧
  Airbender.Compiler.MemoryFrameNative.KeccakCached.native.initializationFields.all (fun field =>
    field.baseFrameCheck Airbender.Compiler.MemoryNative.KeccakCached.native.sourcePlacement Airbender.Compiler.MemoryNative.KeccakCached.native.bank Airbender.Compiler.MemoryFrameNative.KeccakCached.native.allCoordinates Airbender.Compiler.FullArithmeticNative.KeccakCached.native.inputBank Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank) = true ∧
  Airbender.Compiler.MemoryFrameNative.KeccakCached.native.executeFields.all (fun field =>
    field.baseFrameCheck Airbender.Compiler.MemoryNative.KeccakCached.native.sourcePlacement Airbender.Compiler.MemoryNative.KeccakCached.native.bank Airbender.Compiler.MemoryFrameNative.KeccakCached.native.allCoordinates Airbender.Compiler.FullArithmeticNative.KeccakCached.native.inputBank Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank) = true :=
  NumericMemoryFrameChecks.check_sound data Airbender.Compiler.MemoryFrameNative.KeccakCached.native.ramFields Airbender.Compiler.MemoryFrameNative.KeccakCached.native.initializationFields Airbender.Compiler.MemoryFrameNative.KeccakCached.native.executeFields
    Airbender.Compiler.MemoryNative.KeccakCached.native.sourcePlacement Airbender.Compiler.MemoryNative.KeccakCached.native.bank Airbender.Compiler.MemoryFrameNative.KeccakCached.native.activeCoordinates Airbender.Compiler.MemoryFrameNative.KeccakCached.native.allCoordinates
    Airbender.Compiler.FullArithmeticNative.KeccakCached.native.inputBank Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank active_binding all_binding placement_binding nativeAddress_binding inputAddress_binding fullAddress_binding ram_binding initialization_binding execution_binding checked

end Airbender.Compiler.MemoryFrameChecks.KeccakCached
