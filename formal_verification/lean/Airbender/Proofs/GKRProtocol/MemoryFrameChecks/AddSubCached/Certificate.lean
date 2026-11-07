import Airbender.Proofs.GKRProtocol.MemoryFrameChecks.AddSubCached.Bindings

namespace Airbender.Compiler.MemoryFrameChecks.AddSubCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

theorem checked : NumericMemoryFrameChecks.check data = true := by decide +kernel

theorem originalChecked : Airbender.Compiler.MemoryFrameNative.AddSubCached.native.ramFields.all (fun field =>
    field.baseFrameCheck Airbender.Compiler.MemoryNative.AddSubCached.native.sourcePlacement Airbender.Compiler.MemoryNative.AddSubCached.native.bank Airbender.Compiler.MemoryFrameNative.AddSubCached.native.activeCoordinates Airbender.Compiler.FullArithmeticNative.AddSubCached.native.inputBank Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank) = true ∧
  Airbender.Compiler.MemoryFrameNative.AddSubCached.native.initializationFields.all (fun field =>
    field.baseFrameCheck Airbender.Compiler.MemoryNative.AddSubCached.native.sourcePlacement Airbender.Compiler.MemoryNative.AddSubCached.native.bank Airbender.Compiler.MemoryFrameNative.AddSubCached.native.allCoordinates Airbender.Compiler.FullArithmeticNative.AddSubCached.native.inputBank Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank) = true ∧
  Airbender.Compiler.MemoryFrameNative.AddSubCached.native.executeFields.all (fun field =>
    field.baseFrameCheck Airbender.Compiler.MemoryNative.AddSubCached.native.sourcePlacement Airbender.Compiler.MemoryNative.AddSubCached.native.bank Airbender.Compiler.MemoryFrameNative.AddSubCached.native.allCoordinates Airbender.Compiler.FullArithmeticNative.AddSubCached.native.inputBank Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank) = true :=
  NumericMemoryFrameChecks.check_sound_of_binding data Airbender.Compiler.MemoryFrameNative.AddSubCached.native.ramFields Airbender.Compiler.MemoryFrameNative.AddSubCached.native.initializationFields Airbender.Compiler.MemoryFrameNative.AddSubCached.native.executeFields
    Airbender.Compiler.MemoryNative.AddSubCached.native.sourcePlacement Airbender.Compiler.MemoryNative.AddSubCached.native.bank Airbender.Compiler.MemoryFrameNative.AddSubCached.native.activeCoordinates Airbender.Compiler.MemoryFrameNative.AddSubCached.native.allCoordinates
    Airbender.Compiler.FullArithmeticNative.AddSubCached.native.inputBank Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank source_binding checked

end Airbender.Compiler.MemoryFrameChecks.AddSubCached
