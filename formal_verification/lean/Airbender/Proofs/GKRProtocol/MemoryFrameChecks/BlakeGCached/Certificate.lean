import Airbender.Proofs.GKRProtocol.MemoryFrameChecks.BlakeGCached.Bindings

namespace Airbender.Compiler.MemoryFrameChecks.BlakeGCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

theorem checked : NumericMemoryFrameChecks.check data = true := by decide +kernel

theorem originalChecked : Airbender.Compiler.MemoryFrameNative.BlakeGCached.native.ramFields.all (fun field =>
    field.baseFrameCheck Airbender.Compiler.MemoryNative.BlakeGCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeGCached.native.bank Airbender.Compiler.MemoryFrameNative.BlakeGCached.native.activeCoordinates Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.inputBank Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank) = true ∧
  Airbender.Compiler.MemoryFrameNative.BlakeGCached.native.initializationFields.all (fun field =>
    field.baseFrameCheck Airbender.Compiler.MemoryNative.BlakeGCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeGCached.native.bank Airbender.Compiler.MemoryFrameNative.BlakeGCached.native.allCoordinates Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.inputBank Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank) = true ∧
  Airbender.Compiler.MemoryFrameNative.BlakeGCached.native.executeFields.all (fun field =>
    field.baseFrameCheck Airbender.Compiler.MemoryNative.BlakeGCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeGCached.native.bank Airbender.Compiler.MemoryFrameNative.BlakeGCached.native.allCoordinates Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.inputBank Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank) = true :=
  NumericMemoryFrameChecks.check_sound data Airbender.Compiler.MemoryFrameNative.BlakeGCached.native.ramFields Airbender.Compiler.MemoryFrameNative.BlakeGCached.native.initializationFields Airbender.Compiler.MemoryFrameNative.BlakeGCached.native.executeFields
    Airbender.Compiler.MemoryNative.BlakeGCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeGCached.native.bank Airbender.Compiler.MemoryFrameNative.BlakeGCached.native.activeCoordinates Airbender.Compiler.MemoryFrameNative.BlakeGCached.native.allCoordinates
    Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.inputBank Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank active_binding all_binding placement_binding nativeAddress_binding inputAddress_binding fullAddress_binding ram_binding initialization_binding execution_binding checked

end Airbender.Compiler.MemoryFrameChecks.BlakeGCached
