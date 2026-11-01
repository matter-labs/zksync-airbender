import Airbender.Proofs.GKRProtocol.MemoryFrameChecks.ShiftBinopUncached.Data
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.MemoryFrameChecks.ShiftBinopUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def fullAddressSource : Fin 103 → Nat := (fun wire : Fin 103 => if wire.val < 98 then AddressUniqueChecks.addressCode (Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.bank.address wire) else AddressUniqueChecks.addressCode (Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank.address (Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank.placement (Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.bank.address wire))))

numeric_data_binding fullAddressLeaf0 : (data.fullAddress.toList.drop 0).take 32 =
  NumericQueryFrameChecks.window fullAddressSource 0 32 (by decide +kernel)

theorem fullAddressSlice0 : (data.fullAddress.toList.drop 0).take 32 = ((List.ofFn fullAddressSource).drop 0).take 32 :=
  fullAddressLeaf0.trans (NumericQueryFrameChecks.window_binding fullAddressSource 0 32 (by decide +kernel))

numeric_data_binding fullAddressLeaf32 : (data.fullAddress.toList.drop 32).take 32 =
  NumericQueryFrameChecks.window fullAddressSource 32 32 (by decide +kernel)

theorem fullAddressSlice32 : (data.fullAddress.toList.drop 32).take 32 = ((List.ofFn fullAddressSource).drop 32).take 32 :=
  fullAddressLeaf32.trans (NumericQueryFrameChecks.window_binding fullAddressSource 32 32 (by decide +kernel))

numeric_data_binding fullAddressLeaf64 : (data.fullAddress.toList.drop 64).take 32 =
  NumericQueryFrameChecks.window fullAddressSource 64 32 (by decide +kernel)

theorem fullAddressSlice64 : (data.fullAddress.toList.drop 64).take 32 = ((List.ofFn fullAddressSource).drop 64).take 32 :=
  fullAddressLeaf64.trans (NumericQueryFrameChecks.window_binding fullAddressSource 64 32 (by decide +kernel))

numeric_data_binding fullAddressLeaf96 : (data.fullAddress.toList.drop 96).take 7 =
  NumericQueryFrameChecks.window fullAddressSource 96 7 (by decide +kernel)

theorem fullAddressSlice96 : (data.fullAddress.toList.drop 96).take 7 = ((List.ofFn fullAddressSource).drop 96).take 7 :=
  fullAddressLeaf96.trans (NumericQueryFrameChecks.window_binding fullAddressSource 96 7 (by decide +kernel))

theorem fullAddressNode0_64 : (data.fullAddress.toList.drop 0).take 64 = ((List.ofFn fullAddressSource).drop 0).take 64 :=
  NumericQueryFrameChecks.merge_bindings data.fullAddress.toList (List.ofFn fullAddressSource) 0 32 32 fullAddressSlice0 fullAddressSlice32

theorem fullAddressNode64_39 : (data.fullAddress.toList.drop 64).take 39 = ((List.ofFn fullAddressSource).drop 64).take 39 :=
  NumericQueryFrameChecks.merge_bindings data.fullAddress.toList (List.ofFn fullAddressSource) 64 32 7 fullAddressSlice64 fullAddressSlice96

theorem fullAddressNode0_103 : (data.fullAddress.toList.drop 0).take 103 = ((List.ofFn fullAddressSource).drop 0).take 103 :=
  NumericQueryFrameChecks.merge_bindings data.fullAddress.toList (List.ofFn fullAddressSource) 0 64 39 fullAddressNode0_64 fullAddressNode64_39

theorem fullAddress_fast_binding : data.fullAddress.toList = (List.ofFn fullAddressSource) :=
  NumericQueryFrameChecks.complete_binding data.fullAddress.toList (List.ofFn fullAddressSource) 103
    (by decide +kernel) List.length_ofFn fullAddressNode0_103

end Airbender.Compiler.MemoryFrameChecks.ShiftBinopUncached
