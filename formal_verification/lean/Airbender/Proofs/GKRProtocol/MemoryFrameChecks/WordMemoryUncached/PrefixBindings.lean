import Airbender.Proofs.GKRProtocol.MemoryFrameNative.WordMemoryUncachedInputs
import Airbender.Proofs.GKRProtocol.NumericMemoryFramePrefix
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport
namespace Airbender.Compiler.MemoryFrameChecks.WordMemoryUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192
numeric_data_binding memory_inputPrefix : Airbender.Compiler.MemoryNative.WordMemoryUncached.native.addresses.take Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.inputs.length = Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.inputs

theorem inputCoordinates (wire : Fin 58) (inside : wire.val < 52) :
    Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank.address wire = Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.inputBank.address ⟨wire.val, inside⟩ :=
  NumericMemoryFrameChecks.address_getter_prefix Airbender.Compiler.MemoryNative.WordMemoryUncached.native.addresses Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.inputs
    (by decide) memory_inputPrefix ⟨wire.val, inside⟩

theorem inputRoundTrip (wire : Fin 52) :
    Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.inputBank.placement (Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.inputBank.address wire) = wire := by
  apply WireBank.ofList_roundTrip
  rw [← Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.inputPrefix]
  exact Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.addressesUnique.take
end Airbender.Compiler.MemoryFrameChecks.WordMemoryUncached
