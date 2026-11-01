import Airbender.Proofs.GKRProtocol.MemoryFrameChecks.UnifiedUncached.Data
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.MemoryFrameChecks.UnifiedUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def nativeAddressSource : Fin 142 → Nat := (fun wire : Fin 142 => AddressUniqueChecks.addressCode (Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank.address wire))

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

numeric_data_binding nativeAddressLeaf128 : (data.nativeAddress.toList.drop 128).take 14 =
  NumericQueryFrameChecks.window nativeAddressSource 128 14 (by decide +kernel)

theorem nativeAddressSlice128 : (data.nativeAddress.toList.drop 128).take 14 = ((List.ofFn nativeAddressSource).drop 128).take 14 :=
  nativeAddressLeaf128.trans (NumericQueryFrameChecks.window_binding nativeAddressSource 128 14 (by decide +kernel))

theorem nativeAddressNode0_64 : (data.nativeAddress.toList.drop 0).take 64 = ((List.ofFn nativeAddressSource).drop 0).take 64 :=
  NumericQueryFrameChecks.merge_bindings data.nativeAddress.toList (List.ofFn nativeAddressSource) 0 32 32 nativeAddressSlice0 nativeAddressSlice32

theorem nativeAddressNode96_46 : (data.nativeAddress.toList.drop 96).take 46 = ((List.ofFn nativeAddressSource).drop 96).take 46 :=
  NumericQueryFrameChecks.merge_bindings data.nativeAddress.toList (List.ofFn nativeAddressSource) 96 32 14 nativeAddressSlice96 nativeAddressSlice128

theorem nativeAddressNode64_78 : (data.nativeAddress.toList.drop 64).take 78 = ((List.ofFn nativeAddressSource).drop 64).take 78 :=
  NumericQueryFrameChecks.merge_bindings data.nativeAddress.toList (List.ofFn nativeAddressSource) 64 32 46 nativeAddressSlice64 nativeAddressNode96_46

theorem nativeAddressNode0_142 : (data.nativeAddress.toList.drop 0).take 142 = ((List.ofFn nativeAddressSource).drop 0).take 142 :=
  NumericQueryFrameChecks.merge_bindings data.nativeAddress.toList (List.ofFn nativeAddressSource) 0 64 78 nativeAddressNode0_64 nativeAddressNode64_78

theorem nativeAddress_fast_binding : data.nativeAddress.toList = (List.ofFn nativeAddressSource) :=
  NumericQueryFrameChecks.complete_binding data.nativeAddress.toList (List.ofFn nativeAddressSource) 142
    (by decide +kernel) List.length_ofFn nativeAddressNode0_142

end Airbender.Compiler.MemoryFrameChecks.UnifiedUncached
