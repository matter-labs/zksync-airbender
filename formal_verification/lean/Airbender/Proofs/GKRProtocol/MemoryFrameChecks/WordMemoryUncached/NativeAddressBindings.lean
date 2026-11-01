import Airbender.Proofs.GKRProtocol.MemoryFrameChecks.WordMemoryUncached.Data
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.MemoryFrameChecks.WordMemoryUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def nativeAddressSource : Fin 58 → Nat := (fun wire : Fin 58 => AddressUniqueChecks.addressCode (Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank.address wire))

numeric_data_binding nativeAddressLeaf0 : (data.nativeAddress.toList.drop 0).take 32 =
  NumericQueryFrameChecks.window nativeAddressSource 0 32 (by decide +kernel)

theorem nativeAddressSlice0 : (data.nativeAddress.toList.drop 0).take 32 = ((List.ofFn nativeAddressSource).drop 0).take 32 :=
  nativeAddressLeaf0.trans (NumericQueryFrameChecks.window_binding nativeAddressSource 0 32 (by decide +kernel))

numeric_data_binding nativeAddressLeaf32 : (data.nativeAddress.toList.drop 32).take 26 =
  NumericQueryFrameChecks.window nativeAddressSource 32 26 (by decide +kernel)

theorem nativeAddressSlice32 : (data.nativeAddress.toList.drop 32).take 26 = ((List.ofFn nativeAddressSource).drop 32).take 26 :=
  nativeAddressLeaf32.trans (NumericQueryFrameChecks.window_binding nativeAddressSource 32 26 (by decide +kernel))

theorem nativeAddressNode0_58 : (data.nativeAddress.toList.drop 0).take 58 = ((List.ofFn nativeAddressSource).drop 0).take 58 :=
  NumericQueryFrameChecks.merge_bindings data.nativeAddress.toList (List.ofFn nativeAddressSource) 0 32 26 nativeAddressSlice0 nativeAddressSlice32

theorem nativeAddress_fast_binding : data.nativeAddress.toList = (List.ofFn nativeAddressSource) :=
  NumericQueryFrameChecks.complete_binding data.nativeAddress.toList (List.ofFn nativeAddressSource) 58
    (by decide +kernel) List.length_ofFn nativeAddressNode0_58

end Airbender.Compiler.MemoryFrameChecks.WordMemoryUncached
