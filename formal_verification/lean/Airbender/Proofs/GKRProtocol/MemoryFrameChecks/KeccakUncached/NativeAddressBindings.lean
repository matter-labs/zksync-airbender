import Airbender.Proofs.GKRProtocol.MemoryFrameChecks.KeccakUncached.Data
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.MemoryFrameChecks.KeccakUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def nativeAddressSource : Fin 272 → Nat := (fun wire : Fin 272 => AddressUniqueChecks.addressCode (Airbender.Compiler.MemoryNative.KeccakUncached.native.bank.address wire))

numeric_data_binding nativeAddressLeaf0 : (data.nativeAddress.toList.drop 0).take 32 =
  NumericQueryFrameChecks.window nativeAddressSource 0 32 (by decide +kernel)

theorem nativeAddressSlice0 : (data.nativeAddress.toList.drop 0).take 32 = ((List.ofFn nativeAddressSource).drop 0).take 32 :=
  nativeAddressLeaf0.trans (NumericQueryFrameChecks.window_binding nativeAddressSource 0 32 (by decide +kernel))

numeric_data_binding nativeAddressLeaf32 : (data.nativeAddress.toList.drop 32).take 32 =
  NumericQueryFrameChecks.window nativeAddressSource 32 32 (by decide +kernel)

theorem nativeAddressSlice32 : (data.nativeAddress.toList.drop 32).take 32 = ((List.ofFn nativeAddressSource).drop 32).take 32 :=
  nativeAddressLeaf32.trans (NumericQueryFrameChecks.window_binding nativeAddressSource 32 32 (by decide +kernel))

numeric_data_binding nativeAddressLeaf64 : (data.nativeAddress.toList.drop 64).take 32 =
  NumericQueryFrameChecks.window nativeAddressSource 64 32 (by decide +kernel)

theorem nativeAddressSlice64 : (data.nativeAddress.toList.drop 64).take 32 = ((List.ofFn nativeAddressSource).drop 64).take 32 :=
  nativeAddressLeaf64.trans (NumericQueryFrameChecks.window_binding nativeAddressSource 64 32 (by decide +kernel))

numeric_data_binding nativeAddressLeaf96 : (data.nativeAddress.toList.drop 96).take 32 =
  NumericQueryFrameChecks.window nativeAddressSource 96 32 (by decide +kernel)

theorem nativeAddressSlice96 : (data.nativeAddress.toList.drop 96).take 32 = ((List.ofFn nativeAddressSource).drop 96).take 32 :=
  nativeAddressLeaf96.trans (NumericQueryFrameChecks.window_binding nativeAddressSource 96 32 (by decide +kernel))

numeric_data_binding nativeAddressLeaf128 : (data.nativeAddress.toList.drop 128).take 32 =
  NumericQueryFrameChecks.window nativeAddressSource 128 32 (by decide +kernel)

theorem nativeAddressSlice128 : (data.nativeAddress.toList.drop 128).take 32 = ((List.ofFn nativeAddressSource).drop 128).take 32 :=
  nativeAddressLeaf128.trans (NumericQueryFrameChecks.window_binding nativeAddressSource 128 32 (by decide +kernel))

numeric_data_binding nativeAddressLeaf160 : (data.nativeAddress.toList.drop 160).take 32 =
  NumericQueryFrameChecks.window nativeAddressSource 160 32 (by decide +kernel)

theorem nativeAddressSlice160 : (data.nativeAddress.toList.drop 160).take 32 = ((List.ofFn nativeAddressSource).drop 160).take 32 :=
  nativeAddressLeaf160.trans (NumericQueryFrameChecks.window_binding nativeAddressSource 160 32 (by decide +kernel))

numeric_data_binding nativeAddressLeaf192 : (data.nativeAddress.toList.drop 192).take 32 =
  NumericQueryFrameChecks.window nativeAddressSource 192 32 (by decide +kernel)

theorem nativeAddressSlice192 : (data.nativeAddress.toList.drop 192).take 32 = ((List.ofFn nativeAddressSource).drop 192).take 32 :=
  nativeAddressLeaf192.trans (NumericQueryFrameChecks.window_binding nativeAddressSource 192 32 (by decide +kernel))

numeric_data_binding nativeAddressLeaf224 : (data.nativeAddress.toList.drop 224).take 32 =
  NumericQueryFrameChecks.window nativeAddressSource 224 32 (by decide +kernel)

theorem nativeAddressSlice224 : (data.nativeAddress.toList.drop 224).take 32 = ((List.ofFn nativeAddressSource).drop 224).take 32 :=
  nativeAddressLeaf224.trans (NumericQueryFrameChecks.window_binding nativeAddressSource 224 32 (by decide +kernel))

numeric_data_binding nativeAddressLeaf256 : (data.nativeAddress.toList.drop 256).take 16 =
  NumericQueryFrameChecks.window nativeAddressSource 256 16 (by decide +kernel)

theorem nativeAddressSlice256 : (data.nativeAddress.toList.drop 256).take 16 = ((List.ofFn nativeAddressSource).drop 256).take 16 :=
  nativeAddressLeaf256.trans (NumericQueryFrameChecks.window_binding nativeAddressSource 256 16 (by decide +kernel))

theorem nativeAddressNode0_64 : (data.nativeAddress.toList.drop 0).take 64 = ((List.ofFn nativeAddressSource).drop 0).take 64 :=
  NumericQueryFrameChecks.merge_bindings data.nativeAddress.toList (List.ofFn nativeAddressSource) 0 32 32 nativeAddressSlice0 nativeAddressSlice32

theorem nativeAddressNode64_64 : (data.nativeAddress.toList.drop 64).take 64 = ((List.ofFn nativeAddressSource).drop 64).take 64 :=
  NumericQueryFrameChecks.merge_bindings data.nativeAddress.toList (List.ofFn nativeAddressSource) 64 32 32 nativeAddressSlice64 nativeAddressSlice96

theorem nativeAddressNode0_128 : (data.nativeAddress.toList.drop 0).take 128 = ((List.ofFn nativeAddressSource).drop 0).take 128 :=
  NumericQueryFrameChecks.merge_bindings data.nativeAddress.toList (List.ofFn nativeAddressSource) 0 64 64 nativeAddressNode0_64 nativeAddressNode64_64

theorem nativeAddressNode128_64 : (data.nativeAddress.toList.drop 128).take 64 = ((List.ofFn nativeAddressSource).drop 128).take 64 :=
  NumericQueryFrameChecks.merge_bindings data.nativeAddress.toList (List.ofFn nativeAddressSource) 128 32 32 nativeAddressSlice128 nativeAddressSlice160

theorem nativeAddressNode224_48 : (data.nativeAddress.toList.drop 224).take 48 = ((List.ofFn nativeAddressSource).drop 224).take 48 :=
  NumericQueryFrameChecks.merge_bindings data.nativeAddress.toList (List.ofFn nativeAddressSource) 224 32 16 nativeAddressSlice224 nativeAddressSlice256

theorem nativeAddressNode192_80 : (data.nativeAddress.toList.drop 192).take 80 = ((List.ofFn nativeAddressSource).drop 192).take 80 :=
  NumericQueryFrameChecks.merge_bindings data.nativeAddress.toList (List.ofFn nativeAddressSource) 192 32 48 nativeAddressSlice192 nativeAddressNode224_48

theorem nativeAddressNode128_144 : (data.nativeAddress.toList.drop 128).take 144 = ((List.ofFn nativeAddressSource).drop 128).take 144 :=
  NumericQueryFrameChecks.merge_bindings data.nativeAddress.toList (List.ofFn nativeAddressSource) 128 64 80 nativeAddressNode128_64 nativeAddressNode192_80

theorem nativeAddressNode0_272 : (data.nativeAddress.toList.drop 0).take 272 = ((List.ofFn nativeAddressSource).drop 0).take 272 :=
  NumericQueryFrameChecks.merge_bindings data.nativeAddress.toList (List.ofFn nativeAddressSource) 0 128 144 nativeAddressNode0_128 nativeAddressNode128_144

theorem nativeAddress_fast_binding : data.nativeAddress.toList = (List.ofFn nativeAddressSource) :=
  NumericQueryFrameChecks.complete_binding data.nativeAddress.toList (List.ofFn nativeAddressSource) 272
    (by decide +kernel) List.length_ofFn nativeAddressNode0_272

end Airbender.Compiler.MemoryFrameChecks.KeccakUncached
