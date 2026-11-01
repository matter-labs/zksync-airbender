import Airbender.Proofs.GKRProtocol.MemoryFrameNative.JumpBranchUncachedInputs
import Airbender.Proofs.GKRProtocol.NumericMemoryFramePrefix
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport
namespace Airbender.Compiler.MemoryFrameChecks.JumpBranchUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192
numeric_data_binding memory_inputPrefix : Airbender.Compiler.MemoryNative.JumpBranchUncached.native.addresses.take Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.inputs.length = Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.inputs

theorem inputCoordinates (wire : Fin 60) (inside : wire.val < 55) :
    Airbender.Compiler.MemoryNative.JumpBranchUncached.native.bank.address wire = Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.inputBank.address ⟨wire.val, inside⟩ :=
  NumericMemoryFrameChecks.address_getter_prefix Airbender.Compiler.MemoryNative.JumpBranchUncached.native.addresses Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.inputs
    (by decide) memory_inputPrefix ⟨wire.val, inside⟩

theorem inputRoundTrip (wire : Fin 55) :
    Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.inputBank.placement (Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.inputBank.address wire) = wire := by
  apply WireBank.ofList_roundTrip
  rw [← Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.inputPrefix]
  exact Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.addressesUnique.take
end Airbender.Compiler.MemoryFrameChecks.JumpBranchUncached
