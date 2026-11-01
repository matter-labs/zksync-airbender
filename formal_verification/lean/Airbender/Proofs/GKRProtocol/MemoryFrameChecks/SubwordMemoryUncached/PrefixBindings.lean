import Airbender.Proofs.GKRProtocol.MemoryFrameNative.SubwordMemoryUncachedInputs
import Airbender.Proofs.GKRProtocol.NumericMemoryFramePrefix
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport
namespace Airbender.Compiler.MemoryFrameChecks.SubwordMemoryUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192
numeric_data_binding memory_inputPrefix : Airbender.Compiler.MemoryNative.SubwordMemoryUncached.native.addresses.take Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.inputs.length = Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.inputs

theorem inputCoordinates (wire : Fin 72) (inside : wire.val < 68) :
    Airbender.Compiler.MemoryNative.SubwordMemoryUncached.native.bank.address wire = Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.inputBank.address ⟨wire.val, inside⟩ :=
  NumericMemoryFrameChecks.address_getter_prefix Airbender.Compiler.MemoryNative.SubwordMemoryUncached.native.addresses Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.inputs
    (by decide) memory_inputPrefix ⟨wire.val, inside⟩

theorem inputRoundTrip (wire : Fin 68) :
    Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.inputBank.placement (Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.inputBank.address wire) = wire := by
  apply WireBank.ofList_roundTrip
  rw [← Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.inputPrefix]
  exact Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.addressesUnique.take
end Airbender.Compiler.MemoryFrameChecks.SubwordMemoryUncached
