import Airbender.Proofs.GKRProtocol.MemoryFrameChecks.WordMemoryUncached.Data
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.MemoryFrameChecks.WordMemoryUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def inputAddressSource : Fin 58 → Nat := (fun wire : Fin 58 => if wire.val < 52 then AddressUniqueChecks.addressCode (Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank.address wire) else AddressUniqueChecks.addressCode (Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.inputBank.address (Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.inputBank.placement (Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank.address wire))))

numeric_data_binding inputAddressLeaf0 : (data.inputAddress.toList.drop 0).take 32 =
  NumericQueryFrameChecks.window inputAddressSource 0 32 (by decide +kernel)

theorem inputAddressSlice0 : (data.inputAddress.toList.drop 0).take 32 = ((List.ofFn inputAddressSource).drop 0).take 32 :=
  inputAddressLeaf0.trans (NumericQueryFrameChecks.window_binding inputAddressSource 0 32 (by decide +kernel))

numeric_data_binding inputAddressLeaf32 : (data.inputAddress.toList.drop 32).take 26 =
  NumericQueryFrameChecks.window inputAddressSource 32 26 (by decide +kernel)

theorem inputAddressSlice32 : (data.inputAddress.toList.drop 32).take 26 = ((List.ofFn inputAddressSource).drop 32).take 26 :=
  inputAddressLeaf32.trans (NumericQueryFrameChecks.window_binding inputAddressSource 32 26 (by decide +kernel))

theorem inputAddressNode0_58 : (data.inputAddress.toList.drop 0).take 58 = ((List.ofFn inputAddressSource).drop 0).take 58 :=
  NumericQueryFrameChecks.merge_bindings data.inputAddress.toList (List.ofFn inputAddressSource) 0 32 26 inputAddressSlice0 inputAddressSlice32

theorem inputAddress_fast_binding : data.inputAddress.toList = (List.ofFn inputAddressSource) :=
  NumericQueryFrameChecks.complete_binding data.inputAddress.toList (List.ofFn inputAddressSource) 58
    (by decide +kernel) List.length_ofFn inputAddressNode0_58

end Airbender.Compiler.MemoryFrameChecks.WordMemoryUncached
