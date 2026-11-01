import Airbender.Proofs.GKRProtocol.MemoryFrameChecks.SubwordMemoryCached.Data
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.MemoryFrameChecks.SubwordMemoryCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def fullAddressSource : Fin 74 → Nat := (fun wire : Fin 74 => if wire.val < 68 then AddressUniqueChecks.addressCode (Airbender.Compiler.MemoryNative.SubwordMemoryCached.native.bank.address wire) else AddressUniqueChecks.addressCode (Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.bank.placement (Airbender.Compiler.MemoryNative.SubwordMemoryCached.native.bank.address wire))))

numeric_data_binding fullAddressLeaf0 : (data.fullAddress.toList.drop 0).take 32 =
  NumericQueryFrameChecks.window fullAddressSource 0 32 (by decide +kernel)

theorem fullAddressSlice0 : (data.fullAddress.toList.drop 0).take 32 = ((List.ofFn fullAddressSource).drop 0).take 32 :=
  fullAddressLeaf0.trans (NumericQueryFrameChecks.window_binding fullAddressSource 0 32 (by decide +kernel))

numeric_data_binding fullAddressLeaf32 : (data.fullAddress.toList.drop 32).take 32 =
  NumericQueryFrameChecks.window fullAddressSource 32 32 (by decide +kernel)

theorem fullAddressSlice32 : (data.fullAddress.toList.drop 32).take 32 = ((List.ofFn fullAddressSource).drop 32).take 32 :=
  fullAddressLeaf32.trans (NumericQueryFrameChecks.window_binding fullAddressSource 32 32 (by decide +kernel))

numeric_data_binding fullAddressLeaf64 : (data.fullAddress.toList.drop 64).take 10 =
  NumericQueryFrameChecks.window fullAddressSource 64 10 (by decide +kernel)

theorem fullAddressSlice64 : (data.fullAddress.toList.drop 64).take 10 = ((List.ofFn fullAddressSource).drop 64).take 10 :=
  fullAddressLeaf64.trans (NumericQueryFrameChecks.window_binding fullAddressSource 64 10 (by decide +kernel))

theorem fullAddressNode32_42 : (data.fullAddress.toList.drop 32).take 42 = ((List.ofFn fullAddressSource).drop 32).take 42 :=
  NumericQueryFrameChecks.merge_bindings data.fullAddress.toList (List.ofFn fullAddressSource) 32 32 10 fullAddressSlice32 fullAddressSlice64

theorem fullAddressNode0_74 : (data.fullAddress.toList.drop 0).take 74 = ((List.ofFn fullAddressSource).drop 0).take 74 :=
  NumericQueryFrameChecks.merge_bindings data.fullAddress.toList (List.ofFn fullAddressSource) 0 32 42 fullAddressSlice0 fullAddressNode32_42

theorem fullAddress_fast_binding : data.fullAddress.toList = (List.ofFn fullAddressSource) :=
  NumericQueryFrameChecks.complete_binding data.fullAddress.toList (List.ofFn fullAddressSource) 74
    (by decide +kernel) List.length_ofFn fullAddressNode0_74

end Airbender.Compiler.MemoryFrameChecks.SubwordMemoryCached
