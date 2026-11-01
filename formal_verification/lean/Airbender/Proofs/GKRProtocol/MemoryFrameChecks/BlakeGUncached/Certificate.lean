import Airbender.Proofs.GKRProtocol.MemoryFrameChecks.BlakeGUncached.Bindings

namespace Airbender.Compiler.MemoryFrameChecks.BlakeGUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

theorem checked : NumericMemoryFrameChecks.check data = true := by decide +kernel

theorem originalChecked : Airbender.Compiler.MemoryFrameNative.BlakeGUncached.native.ramFields.all (fun field =>
    field.baseFrameCheck Airbender.Compiler.MemoryNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank Airbender.Compiler.MemoryFrameNative.BlakeGUncached.native.activeCoordinates Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.inputBank Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.bank) = true ∧
  Airbender.Compiler.MemoryFrameNative.BlakeGUncached.native.initializationFields.all (fun field =>
    field.baseFrameCheck Airbender.Compiler.MemoryNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank Airbender.Compiler.MemoryFrameNative.BlakeGUncached.native.allCoordinates Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.inputBank Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.bank) = true ∧
  Airbender.Compiler.MemoryFrameNative.BlakeGUncached.native.executeFields.all (fun field =>
    field.baseFrameCheck Airbender.Compiler.MemoryNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank Airbender.Compiler.MemoryFrameNative.BlakeGUncached.native.allCoordinates Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.inputBank Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.bank) = true :=
  NumericMemoryFrameChecks.check_sound data Airbender.Compiler.MemoryFrameNative.BlakeGUncached.native.ramFields Airbender.Compiler.MemoryFrameNative.BlakeGUncached.native.initializationFields Airbender.Compiler.MemoryFrameNative.BlakeGUncached.native.executeFields
    Airbender.Compiler.MemoryNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank Airbender.Compiler.MemoryFrameNative.BlakeGUncached.native.activeCoordinates Airbender.Compiler.MemoryFrameNative.BlakeGUncached.native.allCoordinates
    Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.inputBank Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.bank active_binding all_binding placement_binding nativeAddress_binding inputAddress_binding fullAddress_binding ram_binding initialization_binding execution_binding checked

end Airbender.Compiler.MemoryFrameChecks.BlakeGUncached
