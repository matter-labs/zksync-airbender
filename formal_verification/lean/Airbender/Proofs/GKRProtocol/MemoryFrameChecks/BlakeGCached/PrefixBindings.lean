import Airbender.Proofs.GKRProtocol.MemoryFrameNative.BlakeGCachedInputs
import Airbender.Proofs.GKRProtocol.NumericMemoryFramePrefix
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport
namespace Airbender.Compiler.MemoryFrameChecks.BlakeGCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192
numeric_data_binding memory_inputPrefix : Airbender.Compiler.MemoryNative.BlakeGCached.native.addresses.take Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.inputs.length = Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.inputs

theorem inputCoordinates (wire : Fin 118) (inside : wire.val < 112) :
    Airbender.Compiler.MemoryNative.BlakeGCached.native.bank.address wire = Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.inputBank.address ⟨wire.val, inside⟩ :=
  NumericMemoryFrameChecks.address_getter_prefix Airbender.Compiler.MemoryNative.BlakeGCached.native.addresses Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.inputs
    (by decide) memory_inputPrefix ⟨wire.val, inside⟩

theorem inputRoundTrip (wire : Fin 112) :
    Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.inputBank.placement (Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.inputBank.address wire) = wire := by
  apply WireBank.ofList_roundTrip
  rw [← Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.inputPrefix]
  exact Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.addressesUnique.take
end Airbender.Compiler.MemoryFrameChecks.BlakeGCached
