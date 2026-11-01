import Airbender.Proofs.GKRProtocol.MemoryFrameNative.ShiftBinopUncachedInputs
import Airbender.Proofs.GKRProtocol.NumericMemoryFramePrefix
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport
namespace Airbender.Compiler.MemoryFrameChecks.ShiftBinopUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192
numeric_data_binding memory_inputPrefix : Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.addresses.take Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.inputs.length = Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.inputs

theorem inputCoordinates (wire : Fin 103) (inside : wire.val < 98) :
    Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.bank.address wire = Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.inputBank.address ⟨wire.val, inside⟩ :=
  NumericMemoryFrameChecks.address_getter_prefix Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.addresses Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.inputs
    (by decide) memory_inputPrefix ⟨wire.val, inside⟩

theorem inputRoundTrip (wire : Fin 98) :
    Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.inputBank.placement (Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.inputBank.address wire) = wire := by
  apply WireBank.ofList_roundTrip
  rw [← Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.inputPrefix]
  exact Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.addressesUnique.take
end Airbender.Compiler.MemoryFrameChecks.ShiftBinopUncached
