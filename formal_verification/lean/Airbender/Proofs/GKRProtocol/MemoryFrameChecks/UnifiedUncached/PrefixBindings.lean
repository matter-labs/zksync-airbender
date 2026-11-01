import Airbender.Proofs.GKRProtocol.MemoryFrameNative.UnifiedUncachedInputs
import Airbender.Proofs.GKRProtocol.NumericMemoryFramePrefix
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport
namespace Airbender.Compiler.MemoryFrameChecks.UnifiedUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192
numeric_data_binding memory_inputPrefix : Airbender.Compiler.MemoryNative.UnifiedUncached.native.addresses.take Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.inputs.length = Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.inputs

theorem inputCoordinates (wire : Fin 142) (inside : wire.val < 137) :
    Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank.address wire = Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.inputBank.address ⟨wire.val, inside⟩ :=
  NumericMemoryFrameChecks.address_getter_prefix Airbender.Compiler.MemoryNative.UnifiedUncached.native.addresses Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.inputs
    (by decide) memory_inputPrefix ⟨wire.val, inside⟩

theorem inputRoundTrip (wire : Fin 137) :
    Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.inputBank.placement (Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.inputBank.address wire) = wire := by
  apply WireBank.ofList_roundTrip
  rw [← Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.inputPrefix]
  exact Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.addressesUnique.take
end Airbender.Compiler.MemoryFrameChecks.UnifiedUncached
