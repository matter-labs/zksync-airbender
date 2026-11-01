import Airbender.Proofs.GKRProtocol.MemoryFrameChecks.AddSubUncached.Bindings

namespace Airbender.Compiler.MemoryFrameChecks.AddSubUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

theorem checked : NumericMemoryFrameChecks.check data = true := by decide +kernel

theorem originalChecked : Airbender.Compiler.MemoryFrameNative.AddSubUncached.native.ramFields.all (fun field =>
    field.baseFrameCheck Airbender.Compiler.MemoryNative.AddSubUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.AddSubUncached.native.bank Airbender.Compiler.MemoryFrameNative.AddSubUncached.native.activeCoordinates Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.inputBank Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.bank) = true ∧
  Airbender.Compiler.MemoryFrameNative.AddSubUncached.native.initializationFields.all (fun field =>
    field.baseFrameCheck Airbender.Compiler.MemoryNative.AddSubUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.AddSubUncached.native.bank Airbender.Compiler.MemoryFrameNative.AddSubUncached.native.allCoordinates Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.inputBank Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.bank) = true ∧
  Airbender.Compiler.MemoryFrameNative.AddSubUncached.native.executeFields.all (fun field =>
    field.baseFrameCheck Airbender.Compiler.MemoryNative.AddSubUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.AddSubUncached.native.bank Airbender.Compiler.MemoryFrameNative.AddSubUncached.native.allCoordinates Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.inputBank Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.bank) = true :=
  NumericMemoryFrameChecks.check_sound_of_binding data Airbender.Compiler.MemoryFrameNative.AddSubUncached.native.ramFields Airbender.Compiler.MemoryFrameNative.AddSubUncached.native.initializationFields Airbender.Compiler.MemoryFrameNative.AddSubUncached.native.executeFields
    Airbender.Compiler.MemoryNative.AddSubUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.AddSubUncached.native.bank Airbender.Compiler.MemoryFrameNative.AddSubUncached.native.activeCoordinates Airbender.Compiler.MemoryFrameNative.AddSubUncached.native.allCoordinates
    Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.inputBank Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.bank source_binding checked

end Airbender.Compiler.MemoryFrameChecks.AddSubUncached
