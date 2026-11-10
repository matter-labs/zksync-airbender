import Airbender.Proofs.GKRProtocol.MemoryFrameNative.BlakeRoundCachedInputs
import Airbender.Proofs.GKRProtocol.NumericMemoryFramePrefix
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport
namespace Airbender.Compiler.MemoryFrameChecks.BlakeRoundCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192
numeric_data_binding memory_inputPrefix : Airbender.Compiler.MemoryNative.BlakeRoundCached.native.addresses.take Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.inputs.length = Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.inputs

theorem inputCoordinates (wire : Fin 771) (inside : wire.val < 763) :
    Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank.address wire = Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.inputBank.address ⟨wire.val, inside⟩ :=
  NumericMemoryFrameChecks.address_getter_prefix Airbender.Compiler.MemoryNative.BlakeRoundCached.native.addresses Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.inputs
    (by decide) memory_inputPrefix ⟨wire.val, inside⟩

theorem inputRoundTrip (wire : Fin 763) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.inputBank.placement (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.inputBank.address wire) = wire := by
  apply WireBank.ofList_roundTrip
  rw [← Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.inputPrefix]
  exact Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.addressesUnique.take
end Airbender.Compiler.MemoryFrameChecks.BlakeRoundCached
