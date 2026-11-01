import Airbender.Proofs.GKRProtocol.QueryFrameChecks.KeccakCached.Data
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.QueryFrameChecks.KeccakCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def nativeAddressSource : Fin 228 → Nat := (fun wire : Fin 228 => AddressUniqueChecks.addressCode (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address wire))

numeric_data_binding nativeAddressLeaf0 : (data.nativeAddress.drop 0).take 32 =
  NumericQueryFrameChecks.window nativeAddressSource 0 32 (by decide +kernel)

theorem nativeAddressSlice0 : (data.nativeAddress.drop 0).take 32 = ((List.ofFn nativeAddressSource).drop 0).take 32 :=
  nativeAddressLeaf0.trans (NumericQueryFrameChecks.window_binding nativeAddressSource 0 32 (by decide +kernel))

numeric_data_binding nativeAddressLeaf32 : (data.nativeAddress.drop 32).take 32 =
  NumericQueryFrameChecks.window nativeAddressSource 32 32 (by decide +kernel)

theorem nativeAddressSlice32 : (data.nativeAddress.drop 32).take 32 = ((List.ofFn nativeAddressSource).drop 32).take 32 :=
  nativeAddressLeaf32.trans (NumericQueryFrameChecks.window_binding nativeAddressSource 32 32 (by decide +kernel))

numeric_data_binding nativeAddressLeaf64 : (data.nativeAddress.drop 64).take 32 =
  NumericQueryFrameChecks.window nativeAddressSource 64 32 (by decide +kernel)

theorem nativeAddressSlice64 : (data.nativeAddress.drop 64).take 32 = ((List.ofFn nativeAddressSource).drop 64).take 32 :=
  nativeAddressLeaf64.trans (NumericQueryFrameChecks.window_binding nativeAddressSource 64 32 (by decide +kernel))

numeric_data_binding nativeAddressLeaf96 : (data.nativeAddress.drop 96).take 32 =
  NumericQueryFrameChecks.window nativeAddressSource 96 32 (by decide +kernel)

theorem nativeAddressSlice96 : (data.nativeAddress.drop 96).take 32 = ((List.ofFn nativeAddressSource).drop 96).take 32 :=
  nativeAddressLeaf96.trans (NumericQueryFrameChecks.window_binding nativeAddressSource 96 32 (by decide +kernel))

numeric_data_binding nativeAddressLeaf128 : (data.nativeAddress.drop 128).take 32 =
  NumericQueryFrameChecks.window nativeAddressSource 128 32 (by decide +kernel)

theorem nativeAddressSlice128 : (data.nativeAddress.drop 128).take 32 = ((List.ofFn nativeAddressSource).drop 128).take 32 :=
  nativeAddressLeaf128.trans (NumericQueryFrameChecks.window_binding nativeAddressSource 128 32 (by decide +kernel))

numeric_data_binding nativeAddressLeaf160 : (data.nativeAddress.drop 160).take 32 =
  NumericQueryFrameChecks.window nativeAddressSource 160 32 (by decide +kernel)

theorem nativeAddressSlice160 : (data.nativeAddress.drop 160).take 32 = ((List.ofFn nativeAddressSource).drop 160).take 32 :=
  nativeAddressLeaf160.trans (NumericQueryFrameChecks.window_binding nativeAddressSource 160 32 (by decide +kernel))

numeric_data_binding nativeAddressLeaf192 : (data.nativeAddress.drop 192).take 32 =
  NumericQueryFrameChecks.window nativeAddressSource 192 32 (by decide +kernel)

theorem nativeAddressSlice192 : (data.nativeAddress.drop 192).take 32 = ((List.ofFn nativeAddressSource).drop 192).take 32 :=
  nativeAddressLeaf192.trans (NumericQueryFrameChecks.window_binding nativeAddressSource 192 32 (by decide +kernel))

numeric_data_binding nativeAddressLeaf224 : (data.nativeAddress.drop 224).take 4 =
  NumericQueryFrameChecks.window nativeAddressSource 224 4 (by decide +kernel)

theorem nativeAddressSlice224 : (data.nativeAddress.drop 224).take 4 = ((List.ofFn nativeAddressSource).drop 224).take 4 :=
  nativeAddressLeaf224.trans (NumericQueryFrameChecks.window_binding nativeAddressSource 224 4 (by decide +kernel))

theorem nativeAddressNode0_64 : (data.nativeAddress.drop 0).take 64 = ((List.ofFn nativeAddressSource).drop 0).take 64 :=
  NumericQueryFrameChecks.merge_bindings data.nativeAddress (List.ofFn nativeAddressSource) 0 32 32 nativeAddressSlice0 nativeAddressSlice32

theorem nativeAddressNode64_64 : (data.nativeAddress.drop 64).take 64 = ((List.ofFn nativeAddressSource).drop 64).take 64 :=
  NumericQueryFrameChecks.merge_bindings data.nativeAddress (List.ofFn nativeAddressSource) 64 32 32 nativeAddressSlice64 nativeAddressSlice96

theorem nativeAddressNode0_128 : (data.nativeAddress.drop 0).take 128 = ((List.ofFn nativeAddressSource).drop 0).take 128 :=
  NumericQueryFrameChecks.merge_bindings data.nativeAddress (List.ofFn nativeAddressSource) 0 64 64 nativeAddressNode0_64 nativeAddressNode64_64

theorem nativeAddressNode128_64 : (data.nativeAddress.drop 128).take 64 = ((List.ofFn nativeAddressSource).drop 128).take 64 :=
  NumericQueryFrameChecks.merge_bindings data.nativeAddress (List.ofFn nativeAddressSource) 128 32 32 nativeAddressSlice128 nativeAddressSlice160

theorem nativeAddressNode192_36 : (data.nativeAddress.drop 192).take 36 = ((List.ofFn nativeAddressSource).drop 192).take 36 :=
  NumericQueryFrameChecks.merge_bindings data.nativeAddress (List.ofFn nativeAddressSource) 192 32 4 nativeAddressSlice192 nativeAddressSlice224

theorem nativeAddressNode128_100 : (data.nativeAddress.drop 128).take 100 = ((List.ofFn nativeAddressSource).drop 128).take 100 :=
  NumericQueryFrameChecks.merge_bindings data.nativeAddress (List.ofFn nativeAddressSource) 128 64 36 nativeAddressNode128_64 nativeAddressNode192_36

theorem nativeAddressNode0_228 : (data.nativeAddress.drop 0).take 228 = ((List.ofFn nativeAddressSource).drop 0).take 228 :=
  NumericQueryFrameChecks.merge_bindings data.nativeAddress (List.ofFn nativeAddressSource) 0 128 100 nativeAddressNode0_128 nativeAddressNode128_100

theorem nativeAddress_binding : data.nativeAddress = (List.ofFn nativeAddressSource) :=
  NumericQueryFrameChecks.complete_binding data.nativeAddress (List.ofFn nativeAddressSource) 228
    (by decide +kernel) (List.length_ofFn) nativeAddressNode0_228

end Airbender.Compiler.QueryFrameChecks.KeccakCached
