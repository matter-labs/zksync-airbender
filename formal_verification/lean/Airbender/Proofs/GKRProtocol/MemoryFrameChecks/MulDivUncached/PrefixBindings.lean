import Airbender.Proofs.GKRProtocol.MemoryFrameNative.MulDivUncachedInputs
import Airbender.Proofs.GKRProtocol.NumericMemoryFramePrefix
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport
namespace Airbender.Compiler.MemoryFrameChecks.MulDivUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192
numeric_data_binding memory_inputPrefix : Airbender.Compiler.MemoryNative.MulDivUncached.native.addresses.take Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.inputs.length = Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.inputs

theorem inputCoordinates (wire : Fin 76) (inside : wire.val < 71) :
    Airbender.Compiler.MemoryNative.MulDivUncached.native.bank.address wire = Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.inputBank.address ⟨wire.val, inside⟩ :=
  NumericMemoryFrameChecks.address_getter_prefix Airbender.Compiler.MemoryNative.MulDivUncached.native.addresses Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.inputs
    (by decide) memory_inputPrefix ⟨wire.val, inside⟩

theorem inputRoundTrip (wire : Fin 71) :
    Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.inputBank.placement (Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.inputBank.address wire) = wire := by
  apply WireBank.ofList_roundTrip
  rw [← Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.inputPrefix]
  exact Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.addressesUnique.take
end Airbender.Compiler.MemoryFrameChecks.MulDivUncached
