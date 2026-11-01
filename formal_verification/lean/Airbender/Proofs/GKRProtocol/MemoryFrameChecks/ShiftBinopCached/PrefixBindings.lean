import Airbender.Proofs.GKRProtocol.MemoryFrameNative.ShiftBinopCachedInputs
import Airbender.Proofs.GKRProtocol.NumericMemoryFramePrefix
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport
namespace Airbender.Compiler.MemoryFrameChecks.ShiftBinopCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192
numeric_data_binding memory_inputPrefix : Airbender.Compiler.MemoryNative.ShiftBinopCached.native.addresses.take Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.inputs.length = Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.inputs

theorem inputCoordinates (wire : Fin 105) (inside : wire.val < 98) :
    Airbender.Compiler.MemoryNative.ShiftBinopCached.native.bank.address wire = Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.inputBank.address ⟨wire.val, inside⟩ :=
  NumericMemoryFrameChecks.address_getter_prefix Airbender.Compiler.MemoryNative.ShiftBinopCached.native.addresses Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.inputs
    (by decide) memory_inputPrefix ⟨wire.val, inside⟩

theorem inputRoundTrip (wire : Fin 98) :
    Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.inputBank.placement (Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.inputBank.address wire) = wire := by
  apply WireBank.ofList_roundTrip
  rw [← Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.inputPrefix]
  exact Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.addressesUnique.take
end Airbender.Compiler.MemoryFrameChecks.ShiftBinopCached
