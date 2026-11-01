import Airbender.Proofs.GKRProtocol.MemoryFrameChecks.KeccakUncached.Data
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.MemoryFrameChecks.KeccakUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def fullAddressSource : Fin 272 → Nat := (fun wire : Fin 272 => if wire.val < 266 then AddressUniqueChecks.addressCode (Airbender.Compiler.MemoryNative.KeccakUncached.native.bank.address wire) else AddressUniqueChecks.addressCode (Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank.address (Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank.placement (Airbender.Compiler.MemoryNative.KeccakUncached.native.bank.address wire))))

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

numeric_data_binding fullAddressLeaf256 : (data.fullAddress.toList.drop 256).take 16 =
  NumericQueryFrameChecks.window fullAddressSource 256 16 (by decide +kernel)

theorem fullAddressSlice256 : (data.fullAddress.toList.drop 256).take 16 = ((List.ofFn fullAddressSource).drop 256).take 16 :=
  fullAddressLeaf256.trans (NumericQueryFrameChecks.window_binding fullAddressSource 256 16 (by decide +kernel))

theorem fullAddressNode0_64 : (data.fullAddress.toList.drop 0).take 64 = ((List.ofFn fullAddressSource).drop 0).take 64 :=
  NumericQueryFrameChecks.merge_bindings data.fullAddress.toList (List.ofFn fullAddressSource) 0 32 32 fullAddressSlice0 fullAddressSlice32

theorem fullAddressNode64_64 : (data.fullAddress.toList.drop 64).take 64 = ((List.ofFn fullAddressSource).drop 64).take 64 :=
  NumericQueryFrameChecks.merge_bindings data.fullAddress.toList (List.ofFn fullAddressSource) 64 32 32 fullAddressSlice64 fullAddressSlice96

theorem fullAddressNode0_128 : (data.fullAddress.toList.drop 0).take 128 = ((List.ofFn fullAddressSource).drop 0).take 128 :=
  NumericQueryFrameChecks.merge_bindings data.fullAddress.toList (List.ofFn fullAddressSource) 0 64 64 fullAddressNode0_64 fullAddressNode64_64

theorem fullAddressNode128_64 : (data.fullAddress.toList.drop 128).take 64 = ((List.ofFn fullAddressSource).drop 128).take 64 :=
  NumericQueryFrameChecks.merge_bindings data.fullAddress.toList (List.ofFn fullAddressSource) 128 32 32 fullAddressSlice128 fullAddressSlice160

theorem fullAddressNode224_48 : (data.fullAddress.toList.drop 224).take 48 = ((List.ofFn fullAddressSource).drop 224).take 48 :=
  NumericQueryFrameChecks.merge_bindings data.fullAddress.toList (List.ofFn fullAddressSource) 224 32 16 fullAddressSlice224 fullAddressSlice256

theorem fullAddressNode192_80 : (data.fullAddress.toList.drop 192).take 80 = ((List.ofFn fullAddressSource).drop 192).take 80 :=
  NumericQueryFrameChecks.merge_bindings data.fullAddress.toList (List.ofFn fullAddressSource) 192 32 48 fullAddressSlice192 fullAddressNode224_48

theorem fullAddressNode128_144 : (data.fullAddress.toList.drop 128).take 144 = ((List.ofFn fullAddressSource).drop 128).take 144 :=
  NumericQueryFrameChecks.merge_bindings data.fullAddress.toList (List.ofFn fullAddressSource) 128 64 80 fullAddressNode128_64 fullAddressNode192_80

theorem fullAddressNode0_272 : (data.fullAddress.toList.drop 0).take 272 = ((List.ofFn fullAddressSource).drop 0).take 272 :=
  NumericQueryFrameChecks.merge_bindings data.fullAddress.toList (List.ofFn fullAddressSource) 0 128 144 fullAddressNode0_128 fullAddressNode128_144

theorem fullAddress_fast_binding : data.fullAddress.toList = (List.ofFn fullAddressSource) :=
  NumericQueryFrameChecks.complete_binding data.fullAddress.toList (List.ofFn fullAddressSource) 272
    (by decide +kernel) List.length_ofFn fullAddressNode0_272

end Airbender.Compiler.MemoryFrameChecks.KeccakUncached
