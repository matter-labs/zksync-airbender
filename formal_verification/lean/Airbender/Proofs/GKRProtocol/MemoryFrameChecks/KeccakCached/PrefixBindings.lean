import Airbender.Proofs.GKRProtocol.MemoryFrameNative.KeccakCachedInputs
import Airbender.Proofs.GKRProtocol.NumericMemoryFramePrefix
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport
namespace Airbender.Compiler.MemoryFrameChecks.KeccakCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192
numeric_data_binding memory_inputPrefix : Airbender.Compiler.MemoryNative.KeccakCached.native.addresses.take Airbender.Compiler.FullArithmeticNative.KeccakCached.native.inputs.length = Airbender.Compiler.FullArithmeticNative.KeccakCached.native.inputs

theorem inputCoordinates (wire : Fin 274) (inside : wire.val < 266) :
    Airbender.Compiler.MemoryNative.KeccakCached.native.bank.address wire = Airbender.Compiler.FullArithmeticNative.KeccakCached.native.inputBank.address ⟨wire.val, inside⟩ :=
  NumericMemoryFrameChecks.address_getter_prefix Airbender.Compiler.MemoryNative.KeccakCached.native.addresses Airbender.Compiler.FullArithmeticNative.KeccakCached.native.inputs
    (by decide) memory_inputPrefix ⟨wire.val, inside⟩

theorem inputRoundTrip (wire : Fin 266) :
    Airbender.Compiler.FullArithmeticNative.KeccakCached.native.inputBank.placement (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.inputBank.address wire) = wire := by
  apply WireBank.ofList_roundTrip
  rw [← Airbender.Compiler.FullArithmeticNative.KeccakCached.native.inputPrefix]
  exact Airbender.Compiler.FullArithmeticNative.KeccakCached.native.addressesUnique.take
end Airbender.Compiler.MemoryFrameChecks.KeccakCached
