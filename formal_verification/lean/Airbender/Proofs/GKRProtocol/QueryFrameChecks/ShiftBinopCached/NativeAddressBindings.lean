import Airbender.Proofs.GKRProtocol.QueryFrameChecks.ShiftBinopCached.Data
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.QueryFrameChecks.ShiftBinopCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def nativeAddressSource : Fin 97 → Nat := (fun wire : Fin 97 => AddressUniqueChecks.addressCode (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address wire))

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

numeric_data_binding nativeAddressLeaf96 : (data.nativeAddress.drop 96).take 1 =
  NumericQueryFrameChecks.window nativeAddressSource 96 1 (by decide +kernel)

theorem nativeAddressSlice96 : (data.nativeAddress.drop 96).take 1 = ((List.ofFn nativeAddressSource).drop 96).take 1 :=
  nativeAddressLeaf96.trans (NumericQueryFrameChecks.window_binding nativeAddressSource 96 1 (by decide +kernel))

theorem nativeAddressNode0_64 : (data.nativeAddress.drop 0).take 64 = ((List.ofFn nativeAddressSource).drop 0).take 64 :=
  NumericQueryFrameChecks.merge_bindings data.nativeAddress (List.ofFn nativeAddressSource) 0 32 32 nativeAddressSlice0 nativeAddressSlice32

theorem nativeAddressNode64_33 : (data.nativeAddress.drop 64).take 33 = ((List.ofFn nativeAddressSource).drop 64).take 33 :=
  NumericQueryFrameChecks.merge_bindings data.nativeAddress (List.ofFn nativeAddressSource) 64 32 1 nativeAddressSlice64 nativeAddressSlice96

theorem nativeAddressNode0_97 : (data.nativeAddress.drop 0).take 97 = ((List.ofFn nativeAddressSource).drop 0).take 97 :=
  NumericQueryFrameChecks.merge_bindings data.nativeAddress (List.ofFn nativeAddressSource) 0 64 33 nativeAddressNode0_64 nativeAddressNode64_33

theorem nativeAddress_binding : data.nativeAddress = (List.ofFn nativeAddressSource) :=
  NumericQueryFrameChecks.complete_binding data.nativeAddress (List.ofFn nativeAddressSource) 97
    (by decide +kernel) (List.length_ofFn) nativeAddressNode0_97

end Airbender.Compiler.QueryFrameChecks.ShiftBinopCached
