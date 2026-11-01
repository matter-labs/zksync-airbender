import Airbender.Proofs.GKRProtocol.MemoryFrameChecks.MulDivCached.Data
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.MemoryFrameChecks.MulDivCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def fullAddressSource : Fin 78 → Nat := (fun wire : Fin 78 => if wire.val < 71 then AddressUniqueChecks.addressCode (Airbender.Compiler.MemoryNative.MulDivCached.native.bank.address wire) else AddressUniqueChecks.addressCode (Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.placement (Airbender.Compiler.MemoryNative.MulDivCached.native.bank.address wire))))

numeric_data_binding fullAddressLeaf0 : (data.fullAddress.toList.drop 0).take 32 =
  NumericQueryFrameChecks.window fullAddressSource 0 32 (by decide +kernel)

theorem fullAddressSlice0 : (data.fullAddress.toList.drop 0).take 32 = ((List.ofFn fullAddressSource).drop 0).take 32 :=
  fullAddressLeaf0.trans (NumericQueryFrameChecks.window_binding fullAddressSource 0 32 (by decide +kernel))

numeric_data_binding fullAddressLeaf32 : (data.fullAddress.toList.drop 32).take 32 =
  NumericQueryFrameChecks.window fullAddressSource 32 32 (by decide +kernel)

theorem fullAddressSlice32 : (data.fullAddress.toList.drop 32).take 32 = ((List.ofFn fullAddressSource).drop 32).take 32 :=
  fullAddressLeaf32.trans (NumericQueryFrameChecks.window_binding fullAddressSource 32 32 (by decide +kernel))

numeric_data_binding fullAddressLeaf64 : (data.fullAddress.toList.drop 64).take 14 =
  NumericQueryFrameChecks.window fullAddressSource 64 14 (by decide +kernel)

theorem fullAddressSlice64 : (data.fullAddress.toList.drop 64).take 14 = ((List.ofFn fullAddressSource).drop 64).take 14 :=
  fullAddressLeaf64.trans (NumericQueryFrameChecks.window_binding fullAddressSource 64 14 (by decide +kernel))

theorem fullAddressNode32_46 : (data.fullAddress.toList.drop 32).take 46 = ((List.ofFn fullAddressSource).drop 32).take 46 :=
  NumericQueryFrameChecks.merge_bindings data.fullAddress.toList (List.ofFn fullAddressSource) 32 32 14 fullAddressSlice32 fullAddressSlice64

theorem fullAddressNode0_78 : (data.fullAddress.toList.drop 0).take 78 = ((List.ofFn fullAddressSource).drop 0).take 78 :=
  NumericQueryFrameChecks.merge_bindings data.fullAddress.toList (List.ofFn fullAddressSource) 0 32 46 fullAddressSlice0 fullAddressNode32_46

theorem fullAddress_fast_binding : data.fullAddress.toList = (List.ofFn fullAddressSource) :=
  NumericQueryFrameChecks.complete_binding data.fullAddress.toList (List.ofFn fullAddressSource) 78
    (by decide +kernel) List.length_ofFn fullAddressNode0_78

end Airbender.Compiler.MemoryFrameChecks.MulDivCached
