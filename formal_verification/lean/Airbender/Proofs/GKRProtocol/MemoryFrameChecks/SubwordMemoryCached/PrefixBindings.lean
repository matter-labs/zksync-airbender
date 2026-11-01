import Airbender.Proofs.GKRProtocol.MemoryFrameNative.SubwordMemoryCachedInputs
import Airbender.Proofs.GKRProtocol.NumericMemoryFramePrefix
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport
namespace Airbender.Compiler.MemoryFrameChecks.SubwordMemoryCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192
numeric_data_binding memory_inputPrefix : Airbender.Compiler.MemoryNative.SubwordMemoryCached.native.addresses.take Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.inputs.length = Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.inputs

theorem inputCoordinates (wire : Fin 74) (inside : wire.val < 68) :
    Airbender.Compiler.MemoryNative.SubwordMemoryCached.native.bank.address wire = Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.inputBank.address ⟨wire.val, inside⟩ :=
  NumericMemoryFrameChecks.address_getter_prefix Airbender.Compiler.MemoryNative.SubwordMemoryCached.native.addresses Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.inputs
    (by decide) memory_inputPrefix ⟨wire.val, inside⟩

theorem inputRoundTrip (wire : Fin 68) :
    Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.inputBank.placement (Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.inputBank.address wire) = wire := by
  apply WireBank.ofList_roundTrip
  rw [← Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.inputPrefix]
  exact Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.addressesUnique.take
end Airbender.Compiler.MemoryFrameChecks.SubwordMemoryCached
