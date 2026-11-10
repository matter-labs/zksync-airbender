import Airbender.Proofs.GKRProtocol.QueryFrameChecks.BlakeGCached.Data
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.QueryFrameChecks.BlakeGCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def nativeAddressSource : Fin 87 → Nat := (fun wire : Fin 87 => AddressUniqueChecks.addressCode (Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank.address wire))

numeric_data_binding nativeAddressLeaf0 : (data.nativeAddress.drop 0).take 32 =
  NumericQueryFrameChecks.window nativeAddressSource 0 32 (by decide +kernel)

theorem nativeAddressSlice0 : (data.nativeAddress.drop 0).take 32 = ((List.ofFn nativeAddressSource).drop 0).take 32 :=
  nativeAddressLeaf0.trans (NumericQueryFrameChecks.window_binding nativeAddressSource 0 32 (by decide +kernel))

numeric_data_binding nativeAddressLeaf32 : (data.nativeAddress.drop 32).take 32 =
  NumericQueryFrameChecks.window nativeAddressSource 32 32 (by decide +kernel)

theorem nativeAddressSlice32 : (data.nativeAddress.drop 32).take 32 = ((List.ofFn nativeAddressSource).drop 32).take 32 :=
  nativeAddressLeaf32.trans (NumericQueryFrameChecks.window_binding nativeAddressSource 32 32 (by decide +kernel))

numeric_data_binding nativeAddressLeaf64 : (data.nativeAddress.drop 64).take 23 =
  NumericQueryFrameChecks.window nativeAddressSource 64 23 (by decide +kernel)

theorem nativeAddressSlice64 : (data.nativeAddress.drop 64).take 23 = ((List.ofFn nativeAddressSource).drop 64).take 23 :=
  nativeAddressLeaf64.trans (NumericQueryFrameChecks.window_binding nativeAddressSource 64 23 (by decide +kernel))

theorem nativeAddressNode32_55 : (data.nativeAddress.drop 32).take 55 = ((List.ofFn nativeAddressSource).drop 32).take 55 :=
  NumericQueryFrameChecks.merge_bindings data.nativeAddress (List.ofFn nativeAddressSource) 32 32 23 nativeAddressSlice32 nativeAddressSlice64

theorem nativeAddressNode0_87 : (data.nativeAddress.drop 0).take 87 = ((List.ofFn nativeAddressSource).drop 0).take 87 :=
  NumericQueryFrameChecks.merge_bindings data.nativeAddress (List.ofFn nativeAddressSource) 0 32 55 nativeAddressSlice0 nativeAddressNode32_55

theorem nativeAddress_binding : data.nativeAddress = (List.ofFn nativeAddressSource) :=
  NumericQueryFrameChecks.complete_binding data.nativeAddress (List.ofFn nativeAddressSource) 87
    (by decide +kernel) (List.length_ofFn) nativeAddressNode0_87

end Airbender.Compiler.QueryFrameChecks.BlakeGCached
