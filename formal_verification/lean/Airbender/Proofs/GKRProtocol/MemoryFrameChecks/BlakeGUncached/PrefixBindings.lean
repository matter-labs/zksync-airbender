import Airbender.Proofs.GKRProtocol.MemoryFrameNative.BlakeGUncachedInputs
import Airbender.Proofs.GKRProtocol.NumericMemoryFramePrefix
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport
namespace Airbender.Compiler.MemoryFrameChecks.BlakeGUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192
numeric_data_binding memory_inputPrefix : Airbender.Compiler.MemoryNative.BlakeGUncached.native.addresses.take Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.inputs.length = Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.inputs

theorem inputCoordinates (wire : Fin 118) (inside : wire.val < 112) :
    Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank.address wire = Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.inputBank.address ⟨wire.val, inside⟩ :=
  NumericMemoryFrameChecks.address_getter_prefix Airbender.Compiler.MemoryNative.BlakeGUncached.native.addresses Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.inputs
    (by decide) memory_inputPrefix ⟨wire.val, inside⟩

theorem inputRoundTrip (wire : Fin 112) :
    Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.inputBank.placement (Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.inputBank.address wire) = wire := by
  apply WireBank.ofList_roundTrip
  rw [← Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.inputPrefix]
  exact Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.addressesUnique.take
end Airbender.Compiler.MemoryFrameChecks.BlakeGUncached
