import Airbender.Proofs.GKRProtocol.MemoryFrameNative.WordMemoryCachedInputs
import Airbender.Proofs.GKRProtocol.NumericMemoryFramePrefix
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport
namespace Airbender.Compiler.MemoryFrameChecks.WordMemoryCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192
numeric_data_binding memory_inputPrefix : Airbender.Compiler.MemoryNative.WordMemoryCached.native.addresses.take Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.inputs.length = Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.inputs

theorem inputCoordinates (wire : Fin 60) (inside : wire.val < 52) :
    Airbender.Compiler.MemoryNative.WordMemoryCached.native.bank.address wire = Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.inputBank.address ⟨wire.val, inside⟩ :=
  NumericMemoryFrameChecks.address_getter_prefix Airbender.Compiler.MemoryNative.WordMemoryCached.native.addresses Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.inputs
    (by decide) memory_inputPrefix ⟨wire.val, inside⟩

theorem inputRoundTrip (wire : Fin 52) :
    Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.inputBank.placement (Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.inputBank.address wire) = wire := by
  apply WireBank.ofList_roundTrip
  rw [← Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.inputPrefix]
  exact Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.addressesUnique.take
end Airbender.Compiler.MemoryFrameChecks.WordMemoryCached
