import Airbender.Proofs.GKRProtocol.MemoryFrameChecks.KeccakUncached.Bindings

namespace Airbender.Compiler.MemoryFrameChecks.KeccakUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

theorem checked : NumericMemoryFrameChecks.check data = true := by decide +kernel

theorem originalChecked : Airbender.Compiler.MemoryFrameNative.KeccakUncached.native.ramFields.all (fun field =>
    field.baseFrameCheck Airbender.Compiler.MemoryNative.KeccakUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.MemoryFrameNative.KeccakUncached.native.activeCoordinates Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.inputBank Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank) = true ∧
  Airbender.Compiler.MemoryFrameNative.KeccakUncached.native.initializationFields.all (fun field =>
    field.baseFrameCheck Airbender.Compiler.MemoryNative.KeccakUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.MemoryFrameNative.KeccakUncached.native.allCoordinates Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.inputBank Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank) = true ∧
  Airbender.Compiler.MemoryFrameNative.KeccakUncached.native.executeFields.all (fun field =>
    field.baseFrameCheck Airbender.Compiler.MemoryNative.KeccakUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.MemoryFrameNative.KeccakUncached.native.allCoordinates Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.inputBank Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank) = true :=
  NumericMemoryFrameChecks.check_sound data Airbender.Compiler.MemoryFrameNative.KeccakUncached.native.ramFields Airbender.Compiler.MemoryFrameNative.KeccakUncached.native.initializationFields Airbender.Compiler.MemoryFrameNative.KeccakUncached.native.executeFields
    Airbender.Compiler.MemoryNative.KeccakUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.MemoryFrameNative.KeccakUncached.native.activeCoordinates Airbender.Compiler.MemoryFrameNative.KeccakUncached.native.allCoordinates
    Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.inputBank Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank active_binding all_binding placement_binding nativeAddress_binding inputAddress_binding fullAddress_binding ram_binding initialization_binding execution_binding checked

end Airbender.Compiler.MemoryFrameChecks.KeccakUncached
