import Airbender.Proofs.GKRProtocol.MemoryFrameNative.KeccakUncachedInputs
import Airbender.Proofs.GKRProtocol.NumericMemoryFramePrefix
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport
namespace Airbender.Compiler.MemoryFrameChecks.KeccakUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192
numeric_data_binding memory_inputPrefix : Airbender.Compiler.MemoryNative.KeccakUncached.native.addresses.take Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.inputs.length = Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.inputs

theorem inputCoordinates (wire : Fin 272) (inside : wire.val < 266) :
    Airbender.Compiler.MemoryNative.KeccakUncached.native.bank.address wire = Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.inputBank.address ⟨wire.val, inside⟩ :=
  NumericMemoryFrameChecks.address_getter_prefix Airbender.Compiler.MemoryNative.KeccakUncached.native.addresses Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.inputs
    (by decide) memory_inputPrefix ⟨wire.val, inside⟩

theorem inputRoundTrip (wire : Fin 266) :
    Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.inputBank.placement (Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.inputBank.address wire) = wire := by
  apply WireBank.ofList_roundTrip
  rw [← Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.inputPrefix]
  exact Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.addressesUnique.take
end Airbender.Compiler.MemoryFrameChecks.KeccakUncached
