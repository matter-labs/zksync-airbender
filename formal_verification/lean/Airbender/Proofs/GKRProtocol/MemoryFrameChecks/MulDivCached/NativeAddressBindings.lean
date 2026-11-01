import Airbender.Proofs.GKRProtocol.MemoryFrameChecks.MulDivCached.Data
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.MemoryFrameChecks.MulDivCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def nativeAddressSource : Fin 78 → Nat := (fun wire : Fin 78 => AddressUniqueChecks.addressCode (Airbender.Compiler.MemoryNative.MulDivCached.native.bank.address wire))

numeric_data_binding nativeAddressLeaf0 : (data.nativeAddress.toList.drop 0).take 32 =
  NumericQueryFrameChecks.window nativeAddressSource 0 32 (by decide +kernel)

theorem nativeAddressSlice0 : (data.nativeAddress.toList.drop 0).take 32 = ((List.ofFn nativeAddressSource).drop 0).take 32 :=
  nativeAddressLeaf0.trans (NumericQueryFrameChecks.window_binding nativeAddressSource 0 32 (by decide +kernel))

numeric_data_binding nativeAddressLeaf32 : (data.nativeAddress.toList.drop 32).take 32 =
  NumericQueryFrameChecks.window nativeAddressSource 32 32 (by decide +kernel)

theorem nativeAddressSlice32 : (data.nativeAddress.toList.drop 32).take 32 = ((List.ofFn nativeAddressSource).drop 32).take 32 :=
  nativeAddressLeaf32.trans (NumericQueryFrameChecks.window_binding nativeAddressSource 32 32 (by decide +kernel))

numeric_data_binding nativeAddressLeaf64 : (data.nativeAddress.toList.drop 64).take 14 =
  NumericQueryFrameChecks.window nativeAddressSource 64 14 (by decide +kernel)

theorem nativeAddressSlice64 : (data.nativeAddress.toList.drop 64).take 14 = ((List.ofFn nativeAddressSource).drop 64).take 14 :=
  nativeAddressLeaf64.trans (NumericQueryFrameChecks.window_binding nativeAddressSource 64 14 (by decide +kernel))

theorem nativeAddressNode32_46 : (data.nativeAddress.toList.drop 32).take 46 = ((List.ofFn nativeAddressSource).drop 32).take 46 :=
  NumericQueryFrameChecks.merge_bindings data.nativeAddress.toList (List.ofFn nativeAddressSource) 32 32 14 nativeAddressSlice32 nativeAddressSlice64

theorem nativeAddressNode0_78 : (data.nativeAddress.toList.drop 0).take 78 = ((List.ofFn nativeAddressSource).drop 0).take 78 :=
  NumericQueryFrameChecks.merge_bindings data.nativeAddress.toList (List.ofFn nativeAddressSource) 0 32 46 nativeAddressSlice0 nativeAddressNode32_46

theorem nativeAddress_fast_binding : data.nativeAddress.toList = (List.ofFn nativeAddressSource) :=
  NumericQueryFrameChecks.complete_binding data.nativeAddress.toList (List.ofFn nativeAddressSource) 78
    (by decide +kernel) List.length_ofFn nativeAddressNode0_78

end Airbender.Compiler.MemoryFrameChecks.MulDivCached
