import Airbender.Proofs.GKRProtocol.MemoryFrameNative.BigintCachedInputs
import Airbender.Proofs.GKRProtocol.NumericMemoryFramePrefix
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport
namespace Airbender.Compiler.MemoryFrameChecks.BigintCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192
numeric_data_binding memory_inputPrefix : Airbender.Compiler.MemoryNative.BigintCached.native.addresses.take Airbender.Compiler.FullArithmeticNative.BigintCached.native.inputs.length = Airbender.Compiler.FullArithmeticNative.BigintCached.native.inputs

theorem inputCoordinates (wire : Fin 284) (inside : wire.val < 276) :
    Airbender.Compiler.MemoryNative.BigintCached.native.bank.address wire = Airbender.Compiler.FullArithmeticNative.BigintCached.native.inputBank.address ⟨wire.val, inside⟩ :=
  NumericMemoryFrameChecks.address_getter_prefix Airbender.Compiler.MemoryNative.BigintCached.native.addresses Airbender.Compiler.FullArithmeticNative.BigintCached.native.inputs
    (by decide) memory_inputPrefix ⟨wire.val, inside⟩

theorem inputRoundTrip (wire : Fin 276) :
    Airbender.Compiler.FullArithmeticNative.BigintCached.native.inputBank.placement (Airbender.Compiler.FullArithmeticNative.BigintCached.native.inputBank.address wire) = wire := by
  apply WireBank.ofList_roundTrip
  rw [← Airbender.Compiler.FullArithmeticNative.BigintCached.native.inputPrefix]
  exact Airbender.Compiler.FullArithmeticNative.BigintCached.native.addressesUnique.take
end Airbender.Compiler.MemoryFrameChecks.BigintCached
