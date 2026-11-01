import Airbender.Proofs.GKRProtocol.QueryFrameChecks.ShiftBinopUncached.Data
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.QueryFrameChecks.ShiftBinopUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def nativeAddressSource : Fin 95 → Nat := (fun wire : Fin 95 => AddressUniqueChecks.addressCode (Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank.address wire))

numeric_data_binding nativeAddressLeaf0 : (data.nativeAddress.drop 0).take 32 =
  NumericQueryFrameChecks.window nativeAddressSource 0 32 (by decide +kernel)

theorem nativeAddressSlice0 : (data.nativeAddress.drop 0).take 32 = ((List.ofFn nativeAddressSource).drop 0).take 32 :=
  nativeAddressLeaf0.trans (NumericQueryFrameChecks.window_binding nativeAddressSource 0 32 (by decide +kernel))

numeric_data_binding nativeAddressLeaf32 : (data.nativeAddress.drop 32).take 32 =
  NumericQueryFrameChecks.window nativeAddressSource 32 32 (by decide +kernel)

theorem nativeAddressSlice32 : (data.nativeAddress.drop 32).take 32 = ((List.ofFn nativeAddressSource).drop 32).take 32 :=
  nativeAddressLeaf32.trans (NumericQueryFrameChecks.window_binding nativeAddressSource 32 32 (by decide +kernel))

numeric_data_binding nativeAddressLeaf64 : (data.nativeAddress.drop 64).take 31 =
  NumericQueryFrameChecks.window nativeAddressSource 64 31 (by decide +kernel)

theorem nativeAddressSlice64 : (data.nativeAddress.drop 64).take 31 = ((List.ofFn nativeAddressSource).drop 64).take 31 :=
  nativeAddressLeaf64.trans (NumericQueryFrameChecks.window_binding nativeAddressSource 64 31 (by decide +kernel))

theorem nativeAddressNode32_63 : (data.nativeAddress.drop 32).take 63 = ((List.ofFn nativeAddressSource).drop 32).take 63 :=
  NumericQueryFrameChecks.merge_bindings data.nativeAddress (List.ofFn nativeAddressSource) 32 32 31 nativeAddressSlice32 nativeAddressSlice64

theorem nativeAddressNode0_95 : (data.nativeAddress.drop 0).take 95 = ((List.ofFn nativeAddressSource).drop 0).take 95 :=
  NumericQueryFrameChecks.merge_bindings data.nativeAddress (List.ofFn nativeAddressSource) 0 32 63 nativeAddressSlice0 nativeAddressNode32_63

theorem nativeAddress_binding : data.nativeAddress = (List.ofFn nativeAddressSource) :=
  NumericQueryFrameChecks.complete_binding data.nativeAddress (List.ofFn nativeAddressSource) 95
    (by decide +kernel) (List.length_ofFn) nativeAddressNode0_95

end Airbender.Compiler.QueryFrameChecks.ShiftBinopUncached
