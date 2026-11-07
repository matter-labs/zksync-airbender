import Airbender.Proofs.GKRProtocol.MemoryFrameChecks.BigintCached.Data
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.MemoryFrameChecks.BigintCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def fullAddressSource : Fin 284 → Nat := (fun wire : Fin 284 => if wire.val < 276 then AddressUniqueChecks.addressCode (Airbender.Compiler.MemoryNative.BigintCached.native.bank.address wire) else AddressUniqueChecks.addressCode (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (Airbender.Compiler.MemoryNative.BigintCached.native.bank.address wire))))

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

numeric_data_binding fullAddressLeaf96 : (data.fullAddress.toList.drop 96).take 32 =
  NumericQueryFrameChecks.window fullAddressSource 96 32 (by decide +kernel)

theorem fullAddressSlice96 : (data.fullAddress.toList.drop 96).take 32 = ((List.ofFn fullAddressSource).drop 96).take 32 :=
  fullAddressLeaf96.trans (NumericQueryFrameChecks.window_binding fullAddressSource 96 32 (by decide +kernel))

numeric_data_binding fullAddressLeaf128 : (data.fullAddress.toList.drop 128).take 32 =
  NumericQueryFrameChecks.window fullAddressSource 128 32 (by decide +kernel)

theorem fullAddressSlice128 : (data.fullAddress.toList.drop 128).take 32 = ((List.ofFn fullAddressSource).drop 128).take 32 :=
  fullAddressLeaf128.trans (NumericQueryFrameChecks.window_binding fullAddressSource 128 32 (by decide +kernel))

numeric_data_binding fullAddressLeaf160 : (data.fullAddress.toList.drop 160).take 32 =
  NumericQueryFrameChecks.window fullAddressSource 160 32 (by decide +kernel)

theorem fullAddressSlice160 : (data.fullAddress.toList.drop 160).take 32 = ((List.ofFn fullAddressSource).drop 160).take 32 :=
  fullAddressLeaf160.trans (NumericQueryFrameChecks.window_binding fullAddressSource 160 32 (by decide +kernel))

numeric_data_binding fullAddressLeaf192 : (data.fullAddress.toList.drop 192).take 32 =
  NumericQueryFrameChecks.window fullAddressSource 192 32 (by decide +kernel)

theorem fullAddressSlice192 : (data.fullAddress.toList.drop 192).take 32 = ((List.ofFn fullAddressSource).drop 192).take 32 :=
  fullAddressLeaf192.trans (NumericQueryFrameChecks.window_binding fullAddressSource 192 32 (by decide +kernel))

numeric_data_binding fullAddressLeaf224 : (data.fullAddress.toList.drop 224).take 32 =
  NumericQueryFrameChecks.window fullAddressSource 224 32 (by decide +kernel)

theorem fullAddressSlice224 : (data.fullAddress.toList.drop 224).take 32 = ((List.ofFn fullAddressSource).drop 224).take 32 :=
  fullAddressLeaf224.trans (NumericQueryFrameChecks.window_binding fullAddressSource 224 32 (by decide +kernel))

numeric_data_binding fullAddressLeaf256 : (data.fullAddress.toList.drop 256).take 28 =
  NumericQueryFrameChecks.window fullAddressSource 256 28 (by decide +kernel)

theorem fullAddressSlice256 : (data.fullAddress.toList.drop 256).take 28 = ((List.ofFn fullAddressSource).drop 256).take 28 :=
  fullAddressLeaf256.trans (NumericQueryFrameChecks.window_binding fullAddressSource 256 28 (by decide +kernel))

theorem fullAddressNode0_64 : (data.fullAddress.toList.drop 0).take 64 = ((List.ofFn fullAddressSource).drop 0).take 64 :=
  NumericQueryFrameChecks.merge_bindings data.fullAddress.toList (List.ofFn fullAddressSource) 0 32 32 fullAddressSlice0 fullAddressSlice32

theorem fullAddressNode64_64 : (data.fullAddress.toList.drop 64).take 64 = ((List.ofFn fullAddressSource).drop 64).take 64 :=
  NumericQueryFrameChecks.merge_bindings data.fullAddress.toList (List.ofFn fullAddressSource) 64 32 32 fullAddressSlice64 fullAddressSlice96

theorem fullAddressNode0_128 : (data.fullAddress.toList.drop 0).take 128 = ((List.ofFn fullAddressSource).drop 0).take 128 :=
  NumericQueryFrameChecks.merge_bindings data.fullAddress.toList (List.ofFn fullAddressSource) 0 64 64 fullAddressNode0_64 fullAddressNode64_64

theorem fullAddressNode128_64 : (data.fullAddress.toList.drop 128).take 64 = ((List.ofFn fullAddressSource).drop 128).take 64 :=
  NumericQueryFrameChecks.merge_bindings data.fullAddress.toList (List.ofFn fullAddressSource) 128 32 32 fullAddressSlice128 fullAddressSlice160

theorem fullAddressNode224_60 : (data.fullAddress.toList.drop 224).take 60 = ((List.ofFn fullAddressSource).drop 224).take 60 :=
  NumericQueryFrameChecks.merge_bindings data.fullAddress.toList (List.ofFn fullAddressSource) 224 32 28 fullAddressSlice224 fullAddressSlice256

theorem fullAddressNode192_92 : (data.fullAddress.toList.drop 192).take 92 = ((List.ofFn fullAddressSource).drop 192).take 92 :=
  NumericQueryFrameChecks.merge_bindings data.fullAddress.toList (List.ofFn fullAddressSource) 192 32 60 fullAddressSlice192 fullAddressNode224_60

theorem fullAddressNode128_156 : (data.fullAddress.toList.drop 128).take 156 = ((List.ofFn fullAddressSource).drop 128).take 156 :=
  NumericQueryFrameChecks.merge_bindings data.fullAddress.toList (List.ofFn fullAddressSource) 128 64 92 fullAddressNode128_64 fullAddressNode192_92

theorem fullAddressNode0_284 : (data.fullAddress.toList.drop 0).take 284 = ((List.ofFn fullAddressSource).drop 0).take 284 :=
  NumericQueryFrameChecks.merge_bindings data.fullAddress.toList (List.ofFn fullAddressSource) 0 128 156 fullAddressNode0_128 fullAddressNode128_156

theorem fullAddress_fast_binding : data.fullAddress.toList = (List.ofFn fullAddressSource) :=
  NumericQueryFrameChecks.complete_binding data.fullAddress.toList (List.ofFn fullAddressSource) 284
    (by decide +kernel) List.length_ofFn fullAddressNode0_284

end Airbender.Compiler.MemoryFrameChecks.BigintCached
