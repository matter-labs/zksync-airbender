import Airbender.Proofs.GKRProtocol.MemoryFrameNative.UnifiedCachedInputs
import Airbender.Proofs.GKRProtocol.NumericMemoryFramePrefix
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport
namespace Airbender.Compiler.MemoryFrameChecks.UnifiedCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192
numeric_data_binding memory_inputPrefix : Airbender.Compiler.MemoryNative.UnifiedCached.native.addresses.take Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.inputs.length = Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.inputs

theorem inputCoordinates (wire : Fin 144) (inside : wire.val < 137) :
    Airbender.Compiler.MemoryNative.UnifiedCached.native.bank.address wire = Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.inputBank.address ⟨wire.val, inside⟩ :=
  NumericMemoryFrameChecks.address_getter_prefix Airbender.Compiler.MemoryNative.UnifiedCached.native.addresses Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.inputs
    (by decide) memory_inputPrefix ⟨wire.val, inside⟩

theorem inputRoundTrip (wire : Fin 137) :
    Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.inputBank.placement (Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.inputBank.address wire) = wire := by
  apply WireBank.ofList_roundTrip
  rw [← Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.inputPrefix]
  exact Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.addressesUnique.take
end Airbender.Compiler.MemoryFrameChecks.UnifiedCached
