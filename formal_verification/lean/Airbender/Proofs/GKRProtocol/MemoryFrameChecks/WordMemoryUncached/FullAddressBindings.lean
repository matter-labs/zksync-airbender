import Airbender.Proofs.GKRProtocol.MemoryFrameChecks.WordMemoryUncached.Data
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.MemoryFrameChecks.WordMemoryUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def fullAddressSource : Fin 58 → Nat := (fun wire : Fin 58 => if wire.val < 52 then AddressUniqueChecks.addressCode (Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank.address wire) else AddressUniqueChecks.addressCode (Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.bank.address (Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.bank.placement (Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank.address wire))))

numeric_data_binding fullAddressLeaf0 : (data.fullAddress.toList.drop 0).take 32 =
  NumericQueryFrameChecks.window fullAddressSource 0 32 (by decide +kernel)

theorem fullAddressSlice0 : (data.fullAddress.toList.drop 0).take 32 = ((List.ofFn fullAddressSource).drop 0).take 32 :=
  fullAddressLeaf0.trans (NumericQueryFrameChecks.window_binding fullAddressSource 0 32 (by decide +kernel))

numeric_data_binding fullAddressLeaf32 : (data.fullAddress.toList.drop 32).take 26 =
  NumericQueryFrameChecks.window fullAddressSource 32 26 (by decide +kernel)

theorem fullAddressSlice32 : (data.fullAddress.toList.drop 32).take 26 = ((List.ofFn fullAddressSource).drop 32).take 26 :=
  fullAddressLeaf32.trans (NumericQueryFrameChecks.window_binding fullAddressSource 32 26 (by decide +kernel))

theorem fullAddressNode0_58 : (data.fullAddress.toList.drop 0).take 58 = ((List.ofFn fullAddressSource).drop 0).take 58 :=
  NumericQueryFrameChecks.merge_bindings data.fullAddress.toList (List.ofFn fullAddressSource) 0 32 26 fullAddressSlice0 fullAddressSlice32

theorem fullAddress_fast_binding : data.fullAddress.toList = (List.ofFn fullAddressSource) :=
  NumericQueryFrameChecks.complete_binding data.fullAddress.toList (List.ofFn fullAddressSource) 58
    (by decide +kernel) List.length_ofFn fullAddressNode0_58

end Airbender.Compiler.MemoryFrameChecks.WordMemoryUncached
