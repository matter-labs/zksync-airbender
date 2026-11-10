import Airbender.Proofs.GKRProtocol.MemoryFrameChecks.BigintCached.Data
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.MemoryFrameChecks.BigintCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def inputAddressSource : Fin 284 → Nat := (fun wire : Fin 284 => if wire.val < 276 then AddressUniqueChecks.addressCode (Airbender.Compiler.MemoryNative.BigintCached.native.bank.address wire) else AddressUniqueChecks.addressCode (Airbender.Compiler.FullArithmeticNative.BigintCached.native.inputBank.address (Airbender.Compiler.FullArithmeticNative.BigintCached.native.inputBank.placement (Airbender.Compiler.MemoryNative.BigintCached.native.bank.address wire))))

numeric_data_binding inputAddressLeaf0 : (data.inputAddress.toList.drop 0).take 32 =
  NumericQueryFrameChecks.window inputAddressSource 0 32 (by decide +kernel)

theorem inputAddressSlice0 : (data.inputAddress.toList.drop 0).take 32 = ((List.ofFn inputAddressSource).drop 0).take 32 :=
  inputAddressLeaf0.trans (NumericQueryFrameChecks.window_binding inputAddressSource 0 32 (by decide +kernel))

numeric_data_binding inputAddressLeaf32 : (data.inputAddress.toList.drop 32).take 32 =
  NumericQueryFrameChecks.window inputAddressSource 32 32 (by decide +kernel)

theorem inputAddressSlice32 : (data.inputAddress.toList.drop 32).take 32 = ((List.ofFn inputAddressSource).drop 32).take 32 :=
  inputAddressLeaf32.trans (NumericQueryFrameChecks.window_binding inputAddressSource 32 32 (by decide +kernel))

numeric_data_binding inputAddressLeaf64 : (data.inputAddress.toList.drop 64).take 32 =
  NumericQueryFrameChecks.window inputAddressSource 64 32 (by decide +kernel)

theorem inputAddressSlice64 : (data.inputAddress.toList.drop 64).take 32 = ((List.ofFn inputAddressSource).drop 64).take 32 :=
  inputAddressLeaf64.trans (NumericQueryFrameChecks.window_binding inputAddressSource 64 32 (by decide +kernel))

numeric_data_binding inputAddressLeaf96 : (data.inputAddress.toList.drop 96).take 32 =
  NumericQueryFrameChecks.window inputAddressSource 96 32 (by decide +kernel)

theorem inputAddressSlice96 : (data.inputAddress.toList.drop 96).take 32 = ((List.ofFn inputAddressSource).drop 96).take 32 :=
  inputAddressLeaf96.trans (NumericQueryFrameChecks.window_binding inputAddressSource 96 32 (by decide +kernel))

numeric_data_binding inputAddressLeaf128 : (data.inputAddress.toList.drop 128).take 32 =
  NumericQueryFrameChecks.window inputAddressSource 128 32 (by decide +kernel)

theorem inputAddressSlice128 : (data.inputAddress.toList.drop 128).take 32 = ((List.ofFn inputAddressSource).drop 128).take 32 :=
  inputAddressLeaf128.trans (NumericQueryFrameChecks.window_binding inputAddressSource 128 32 (by decide +kernel))

numeric_data_binding inputAddressLeaf160 : (data.inputAddress.toList.drop 160).take 32 =
  NumericQueryFrameChecks.window inputAddressSource 160 32 (by decide +kernel)

theorem inputAddressSlice160 : (data.inputAddress.toList.drop 160).take 32 = ((List.ofFn inputAddressSource).drop 160).take 32 :=
  inputAddressLeaf160.trans (NumericQueryFrameChecks.window_binding inputAddressSource 160 32 (by decide +kernel))

numeric_data_binding inputAddressLeaf192 : (data.inputAddress.toList.drop 192).take 32 =
  NumericQueryFrameChecks.window inputAddressSource 192 32 (by decide +kernel)

theorem inputAddressSlice192 : (data.inputAddress.toList.drop 192).take 32 = ((List.ofFn inputAddressSource).drop 192).take 32 :=
  inputAddressLeaf192.trans (NumericQueryFrameChecks.window_binding inputAddressSource 192 32 (by decide +kernel))

numeric_data_binding inputAddressLeaf224 : (data.inputAddress.toList.drop 224).take 32 =
  NumericQueryFrameChecks.window inputAddressSource 224 32 (by decide +kernel)

theorem inputAddressSlice224 : (data.inputAddress.toList.drop 224).take 32 = ((List.ofFn inputAddressSource).drop 224).take 32 :=
  inputAddressLeaf224.trans (NumericQueryFrameChecks.window_binding inputAddressSource 224 32 (by decide +kernel))

numeric_data_binding inputAddressLeaf256 : (data.inputAddress.toList.drop 256).take 28 =
  NumericQueryFrameChecks.window inputAddressSource 256 28 (by decide +kernel)

theorem inputAddressSlice256 : (data.inputAddress.toList.drop 256).take 28 = ((List.ofFn inputAddressSource).drop 256).take 28 :=
  inputAddressLeaf256.trans (NumericQueryFrameChecks.window_binding inputAddressSource 256 28 (by decide +kernel))

theorem inputAddressNode0_64 : (data.inputAddress.toList.drop 0).take 64 = ((List.ofFn inputAddressSource).drop 0).take 64 :=
  NumericQueryFrameChecks.merge_bindings data.inputAddress.toList (List.ofFn inputAddressSource) 0 32 32 inputAddressSlice0 inputAddressSlice32

theorem inputAddressNode64_64 : (data.inputAddress.toList.drop 64).take 64 = ((List.ofFn inputAddressSource).drop 64).take 64 :=
  NumericQueryFrameChecks.merge_bindings data.inputAddress.toList (List.ofFn inputAddressSource) 64 32 32 inputAddressSlice64 inputAddressSlice96

theorem inputAddressNode0_128 : (data.inputAddress.toList.drop 0).take 128 = ((List.ofFn inputAddressSource).drop 0).take 128 :=
  NumericQueryFrameChecks.merge_bindings data.inputAddress.toList (List.ofFn inputAddressSource) 0 64 64 inputAddressNode0_64 inputAddressNode64_64

theorem inputAddressNode128_64 : (data.inputAddress.toList.drop 128).take 64 = ((List.ofFn inputAddressSource).drop 128).take 64 :=
  NumericQueryFrameChecks.merge_bindings data.inputAddress.toList (List.ofFn inputAddressSource) 128 32 32 inputAddressSlice128 inputAddressSlice160

theorem inputAddressNode224_60 : (data.inputAddress.toList.drop 224).take 60 = ((List.ofFn inputAddressSource).drop 224).take 60 :=
  NumericQueryFrameChecks.merge_bindings data.inputAddress.toList (List.ofFn inputAddressSource) 224 32 28 inputAddressSlice224 inputAddressSlice256

theorem inputAddressNode192_92 : (data.inputAddress.toList.drop 192).take 92 = ((List.ofFn inputAddressSource).drop 192).take 92 :=
  NumericQueryFrameChecks.merge_bindings data.inputAddress.toList (List.ofFn inputAddressSource) 192 32 60 inputAddressSlice192 inputAddressNode224_60

theorem inputAddressNode128_156 : (data.inputAddress.toList.drop 128).take 156 = ((List.ofFn inputAddressSource).drop 128).take 156 :=
  NumericQueryFrameChecks.merge_bindings data.inputAddress.toList (List.ofFn inputAddressSource) 128 64 92 inputAddressNode128_64 inputAddressNode192_92

theorem inputAddressNode0_284 : (data.inputAddress.toList.drop 0).take 284 = ((List.ofFn inputAddressSource).drop 0).take 284 :=
  NumericQueryFrameChecks.merge_bindings data.inputAddress.toList (List.ofFn inputAddressSource) 0 128 156 inputAddressNode0_128 inputAddressNode128_156

theorem inputAddress_fast_binding : data.inputAddress.toList = (List.ofFn inputAddressSource) :=
  NumericQueryFrameChecks.complete_binding data.inputAddress.toList (List.ofFn inputAddressSource) 284
    (by decide +kernel) List.length_ofFn inputAddressNode0_284

end Airbender.Compiler.MemoryFrameChecks.BigintCached
