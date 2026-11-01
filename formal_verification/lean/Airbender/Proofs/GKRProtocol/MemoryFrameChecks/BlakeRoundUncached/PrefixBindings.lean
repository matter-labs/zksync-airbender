import Airbender.Proofs.GKRProtocol.MemoryFrameNative.BlakeRoundUncachedInputs
import Airbender.Proofs.GKRProtocol.NumericMemoryFramePrefix
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport
namespace Airbender.Compiler.MemoryFrameChecks.BlakeRoundUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192
numeric_data_binding memory_inputPrefix : Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.addresses.take Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.inputs.length = Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.inputs

theorem inputCoordinates (wire : Fin 771) (inside : wire.val < 763) :
    Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank.address wire = Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.inputBank.address ⟨wire.val, inside⟩ :=
  NumericMemoryFrameChecks.address_getter_prefix Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.addresses Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.inputs
    (by decide) memory_inputPrefix ⟨wire.val, inside⟩

theorem inputRoundTrip (wire : Fin 763) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.inputBank.placement (Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.inputBank.address wire) = wire := by
  apply WireBank.ofList_roundTrip
  rw [← Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.inputPrefix]
  exact Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.addressesUnique.take
end Airbender.Compiler.MemoryFrameChecks.BlakeRoundUncached
