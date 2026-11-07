import Airbender.Proofs.GKRProtocol.QueryFrameChecks.BigintCached.Data
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.QueryFrameChecks.BigintCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def nativeAddressSource : Fin 222 → Nat := (fun wire : Fin 222 => AddressUniqueChecks.addressCode (Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.address wire))

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

numeric_data_binding nativeAddressLeaf192 : (data.nativeAddress.drop 192).take 30 =
  NumericQueryFrameChecks.window nativeAddressSource 192 30 (by decide +kernel)

theorem nativeAddressSlice192 : (data.nativeAddress.drop 192).take 30 = ((List.ofFn nativeAddressSource).drop 192).take 30 :=
  nativeAddressLeaf192.trans (NumericQueryFrameChecks.window_binding nativeAddressSource 192 30 (by decide +kernel))

theorem nativeAddressNode32_64 : (data.nativeAddress.drop 32).take 64 = ((List.ofFn nativeAddressSource).drop 32).take 64 :=
  NumericQueryFrameChecks.merge_bindings data.nativeAddress (List.ofFn nativeAddressSource) 32 32 32 nativeAddressSlice32 nativeAddressSlice64

theorem nativeAddressNode0_96 : (data.nativeAddress.drop 0).take 96 = ((List.ofFn nativeAddressSource).drop 0).take 96 :=
  NumericQueryFrameChecks.merge_bindings data.nativeAddress (List.ofFn nativeAddressSource) 0 32 64 nativeAddressSlice0 nativeAddressNode32_64

theorem nativeAddressNode96_64 : (data.nativeAddress.drop 96).take 64 = ((List.ofFn nativeAddressSource).drop 96).take 64 :=
  NumericQueryFrameChecks.merge_bindings data.nativeAddress (List.ofFn nativeAddressSource) 96 32 32 nativeAddressSlice96 nativeAddressSlice128

theorem nativeAddressNode160_62 : (data.nativeAddress.drop 160).take 62 = ((List.ofFn nativeAddressSource).drop 160).take 62 :=
  NumericQueryFrameChecks.merge_bindings data.nativeAddress (List.ofFn nativeAddressSource) 160 32 30 nativeAddressSlice160 nativeAddressSlice192

theorem nativeAddressNode96_126 : (data.nativeAddress.drop 96).take 126 = ((List.ofFn nativeAddressSource).drop 96).take 126 :=
  NumericQueryFrameChecks.merge_bindings data.nativeAddress (List.ofFn nativeAddressSource) 96 64 62 nativeAddressNode96_64 nativeAddressNode160_62

theorem nativeAddressNode0_222 : (data.nativeAddress.drop 0).take 222 = ((List.ofFn nativeAddressSource).drop 0).take 222 :=
  NumericQueryFrameChecks.merge_bindings data.nativeAddress (List.ofFn nativeAddressSource) 0 96 126 nativeAddressNode0_96 nativeAddressNode96_126

theorem nativeAddress_binding : data.nativeAddress = (List.ofFn nativeAddressSource) :=
  NumericQueryFrameChecks.complete_binding data.nativeAddress (List.ofFn nativeAddressSource) 222
    (by decide +kernel) (List.length_ofFn) nativeAddressNode0_222

end Airbender.Compiler.QueryFrameChecks.BigintCached
