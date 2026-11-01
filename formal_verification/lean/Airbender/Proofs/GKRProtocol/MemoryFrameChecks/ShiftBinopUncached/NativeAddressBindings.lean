import Airbender.Proofs.GKRProtocol.MemoryFrameChecks.ShiftBinopUncached.Data
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.MemoryFrameChecks.ShiftBinopUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def nativeAddressSource : Fin 103 → Nat := (fun wire : Fin 103 => AddressUniqueChecks.addressCode (Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.bank.address wire))

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

numeric_data_binding nativeAddressLeaf96 : (data.nativeAddress.toList.drop 96).take 7 =
  NumericQueryFrameChecks.window nativeAddressSource 96 7 (by decide +kernel)

theorem nativeAddressSlice96 : (data.nativeAddress.toList.drop 96).take 7 = ((List.ofFn nativeAddressSource).drop 96).take 7 :=
  nativeAddressLeaf96.trans (NumericQueryFrameChecks.window_binding nativeAddressSource 96 7 (by decide +kernel))

theorem nativeAddressNode0_64 : (data.nativeAddress.toList.drop 0).take 64 = ((List.ofFn nativeAddressSource).drop 0).take 64 :=
  NumericQueryFrameChecks.merge_bindings data.nativeAddress.toList (List.ofFn nativeAddressSource) 0 32 32 nativeAddressSlice0 nativeAddressSlice32

theorem nativeAddressNode64_39 : (data.nativeAddress.toList.drop 64).take 39 = ((List.ofFn nativeAddressSource).drop 64).take 39 :=
  NumericQueryFrameChecks.merge_bindings data.nativeAddress.toList (List.ofFn nativeAddressSource) 64 32 7 nativeAddressSlice64 nativeAddressSlice96

theorem nativeAddressNode0_103 : (data.nativeAddress.toList.drop 0).take 103 = ((List.ofFn nativeAddressSource).drop 0).take 103 :=
  NumericQueryFrameChecks.merge_bindings data.nativeAddress.toList (List.ofFn nativeAddressSource) 0 64 39 nativeAddressNode0_64 nativeAddressNode64_39

theorem nativeAddress_fast_binding : data.nativeAddress.toList = (List.ofFn nativeAddressSource) :=
  NumericQueryFrameChecks.complete_binding data.nativeAddress.toList (List.ofFn nativeAddressSource) 103
    (by decide +kernel) List.length_ofFn nativeAddressNode0_103

end Airbender.Compiler.MemoryFrameChecks.ShiftBinopUncached
