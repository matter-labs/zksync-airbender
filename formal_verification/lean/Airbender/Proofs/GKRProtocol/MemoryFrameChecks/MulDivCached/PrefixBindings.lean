import Airbender.Proofs.GKRProtocol.MemoryFrameNative.MulDivCachedInputs
import Airbender.Proofs.GKRProtocol.NumericMemoryFramePrefix
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport
namespace Airbender.Compiler.MemoryFrameChecks.MulDivCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192
numeric_data_binding memory_inputPrefix : Airbender.Compiler.MemoryNative.MulDivCached.native.addresses.take Airbender.Compiler.FullArithmeticNative.MulDivCached.native.inputs.length = Airbender.Compiler.FullArithmeticNative.MulDivCached.native.inputs

theorem inputCoordinates (wire : Fin 78) (inside : wire.val < 71) :
    Airbender.Compiler.MemoryNative.MulDivCached.native.bank.address wire = Airbender.Compiler.FullArithmeticNative.MulDivCached.native.inputBank.address ⟨wire.val, inside⟩ :=
  NumericMemoryFrameChecks.address_getter_prefix Airbender.Compiler.MemoryNative.MulDivCached.native.addresses Airbender.Compiler.FullArithmeticNative.MulDivCached.native.inputs
    (by decide) memory_inputPrefix ⟨wire.val, inside⟩

theorem inputRoundTrip (wire : Fin 71) :
    Airbender.Compiler.FullArithmeticNative.MulDivCached.native.inputBank.placement (Airbender.Compiler.FullArithmeticNative.MulDivCached.native.inputBank.address wire) = wire := by
  apply WireBank.ofList_roundTrip
  rw [← Airbender.Compiler.FullArithmeticNative.MulDivCached.native.inputPrefix]
  exact Airbender.Compiler.FullArithmeticNative.MulDivCached.native.addressesUnique.take
end Airbender.Compiler.MemoryFrameChecks.MulDivCached
