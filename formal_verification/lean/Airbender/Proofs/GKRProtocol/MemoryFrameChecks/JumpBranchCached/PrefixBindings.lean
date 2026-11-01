import Airbender.Proofs.GKRProtocol.MemoryFrameNative.JumpBranchCachedInputs
import Airbender.Proofs.GKRProtocol.NumericMemoryFramePrefix
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport
namespace Airbender.Compiler.MemoryFrameChecks.JumpBranchCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192
numeric_data_binding memory_inputPrefix : Airbender.Compiler.MemoryNative.JumpBranchCached.native.addresses.take Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.inputs.length = Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.inputs

theorem inputCoordinates (wire : Fin 62) (inside : wire.val < 55) :
    Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank.address wire = Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.inputBank.address ⟨wire.val, inside⟩ :=
  NumericMemoryFrameChecks.address_getter_prefix Airbender.Compiler.MemoryNative.JumpBranchCached.native.addresses Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.inputs
    (by decide) memory_inputPrefix ⟨wire.val, inside⟩

theorem inputRoundTrip (wire : Fin 55) :
    Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.inputBank.placement (Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.inputBank.address wire) = wire := by
  apply WireBank.ofList_roundTrip
  rw [← Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.inputPrefix]
  exact Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.addressesUnique.take
end Airbender.Compiler.MemoryFrameChecks.JumpBranchCached
