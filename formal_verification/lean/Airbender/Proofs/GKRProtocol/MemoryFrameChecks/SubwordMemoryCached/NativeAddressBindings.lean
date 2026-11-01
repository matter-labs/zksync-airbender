import Airbender.Proofs.GKRProtocol.MemoryFrameChecks.SubwordMemoryCached.Data
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.MemoryFrameChecks.SubwordMemoryCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def nativeAddressSource : Fin 74 → Nat := (fun wire : Fin 74 => AddressUniqueChecks.addressCode (Airbender.Compiler.MemoryNative.SubwordMemoryCached.native.bank.address wire))

numeric_data_binding nativeAddressLeaf0 : (data.nativeAddress.toList.drop 0).take 32 =
  NumericQueryFrameChecks.window nativeAddressSource 0 32 (by decide +kernel)

theorem nativeAddressSlice0 : (data.nativeAddress.toList.drop 0).take 32 = ((List.ofFn nativeAddressSource).drop 0).take 32 :=
  nativeAddressLeaf0.trans (NumericQueryFrameChecks.window_binding nativeAddressSource 0 32 (by decide +kernel))

numeric_data_binding nativeAddressLeaf32 : (data.nativeAddress.toList.drop 32).take 32 =
  NumericQueryFrameChecks.window nativeAddressSource 32 32 (by decide +kernel)

theorem nativeAddressSlice32 : (data.nativeAddress.toList.drop 32).take 32 = ((List.ofFn nativeAddressSource).drop 32).take 32 :=
  nativeAddressLeaf32.trans (NumericQueryFrameChecks.window_binding nativeAddressSource 32 32 (by decide +kernel))

numeric_data_binding nativeAddressLeaf64 : (data.nativeAddress.toList.drop 64).take 10 =
  NumericQueryFrameChecks.window nativeAddressSource 64 10 (by decide +kernel)

theorem nativeAddressSlice64 : (data.nativeAddress.toList.drop 64).take 10 = ((List.ofFn nativeAddressSource).drop 64).take 10 :=
  nativeAddressLeaf64.trans (NumericQueryFrameChecks.window_binding nativeAddressSource 64 10 (by decide +kernel))

theorem nativeAddressNode32_42 : (data.nativeAddress.toList.drop 32).take 42 = ((List.ofFn nativeAddressSource).drop 32).take 42 :=
  NumericQueryFrameChecks.merge_bindings data.nativeAddress.toList (List.ofFn nativeAddressSource) 32 32 10 nativeAddressSlice32 nativeAddressSlice64

theorem nativeAddressNode0_74 : (data.nativeAddress.toList.drop 0).take 74 = ((List.ofFn nativeAddressSource).drop 0).take 74 :=
  NumericQueryFrameChecks.merge_bindings data.nativeAddress.toList (List.ofFn nativeAddressSource) 0 32 42 nativeAddressSlice0 nativeAddressNode32_42

theorem nativeAddress_fast_binding : data.nativeAddress.toList = (List.ofFn nativeAddressSource) :=
  NumericQueryFrameChecks.complete_binding data.nativeAddress.toList (List.ofFn nativeAddressSource) 74
    (by decide +kernel) List.length_ofFn nativeAddressNode0_74

end Airbender.Compiler.MemoryFrameChecks.SubwordMemoryCached
