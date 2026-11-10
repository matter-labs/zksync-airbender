import Airbender.Proofs.GKRProtocol.MemoryFrameChecks.BlakeRoundCached.Bindings

namespace Airbender.Compiler.MemoryFrameChecks.BlakeRoundCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

theorem checked : NumericMemoryFrameChecks.check data = true := by decide +kernel

theorem originalChecked : Airbender.Compiler.MemoryFrameNative.BlakeRoundCached.native.ramFields.all (fun field =>
    field.baseFrameCheck Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryFrameNative.BlakeRoundCached.native.activeCoordinates Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.inputBank Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank) = true ∧
  Airbender.Compiler.MemoryFrameNative.BlakeRoundCached.native.initializationFields.all (fun field =>
    field.baseFrameCheck Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryFrameNative.BlakeRoundCached.native.allCoordinates Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.inputBank Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank) = true ∧
  Airbender.Compiler.MemoryFrameNative.BlakeRoundCached.native.executeFields.all (fun field =>
    field.baseFrameCheck Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryFrameNative.BlakeRoundCached.native.allCoordinates Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.inputBank Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank) = true :=
  NumericMemoryFrameChecks.check_sound data Airbender.Compiler.MemoryFrameNative.BlakeRoundCached.native.ramFields Airbender.Compiler.MemoryFrameNative.BlakeRoundCached.native.initializationFields Airbender.Compiler.MemoryFrameNative.BlakeRoundCached.native.executeFields
    Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryFrameNative.BlakeRoundCached.native.activeCoordinates Airbender.Compiler.MemoryFrameNative.BlakeRoundCached.native.allCoordinates
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.inputBank Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank active_binding all_binding placement_binding nativeAddress_binding inputAddress_binding fullAddress_binding ram_binding initialization_binding execution_binding checked

end Airbender.Compiler.MemoryFrameChecks.BlakeRoundCached
