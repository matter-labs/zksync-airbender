import Airbender.Proofs.GKRProtocol.MemoryFrameChecks.SubwordMemoryUncached.Bindings

namespace Airbender.Compiler.MemoryFrameChecks.SubwordMemoryUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

theorem checked : NumericMemoryFrameChecks.check data = true := by decide +kernel

theorem originalChecked : Airbender.Compiler.MemoryFrameNative.SubwordMemoryUncached.native.ramFields.all (fun field =>
    field.baseFrameCheck Airbender.Compiler.MemoryNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.SubwordMemoryUncached.native.bank Airbender.Compiler.MemoryFrameNative.SubwordMemoryUncached.native.activeCoordinates Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.inputBank Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.bank) = true ∧
  Airbender.Compiler.MemoryFrameNative.SubwordMemoryUncached.native.initializationFields.all (fun field =>
    field.baseFrameCheck Airbender.Compiler.MemoryNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.SubwordMemoryUncached.native.bank Airbender.Compiler.MemoryFrameNative.SubwordMemoryUncached.native.allCoordinates Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.inputBank Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.bank) = true ∧
  Airbender.Compiler.MemoryFrameNative.SubwordMemoryUncached.native.executeFields.all (fun field =>
    field.baseFrameCheck Airbender.Compiler.MemoryNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.SubwordMemoryUncached.native.bank Airbender.Compiler.MemoryFrameNative.SubwordMemoryUncached.native.allCoordinates Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.inputBank Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.bank) = true :=
  NumericMemoryFrameChecks.check_sound data Airbender.Compiler.MemoryFrameNative.SubwordMemoryUncached.native.ramFields Airbender.Compiler.MemoryFrameNative.SubwordMemoryUncached.native.initializationFields Airbender.Compiler.MemoryFrameNative.SubwordMemoryUncached.native.executeFields
    Airbender.Compiler.MemoryNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.SubwordMemoryUncached.native.bank Airbender.Compiler.MemoryFrameNative.SubwordMemoryUncached.native.activeCoordinates Airbender.Compiler.MemoryFrameNative.SubwordMemoryUncached.native.allCoordinates
    Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.inputBank Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.bank active_binding all_binding placement_binding nativeAddress_binding inputAddress_binding fullAddress_binding ram_binding initialization_binding execution_binding checked

end Airbender.Compiler.MemoryFrameChecks.SubwordMemoryUncached
