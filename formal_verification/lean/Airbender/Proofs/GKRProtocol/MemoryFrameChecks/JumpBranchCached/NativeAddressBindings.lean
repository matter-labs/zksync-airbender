import Airbender.Proofs.GKRProtocol.MemoryFrameChecks.JumpBranchCached.Data
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.MemoryFrameChecks.JumpBranchCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def nativeAddressSource : Fin 62 → Nat := (fun wire : Fin 62 => AddressUniqueChecks.addressCode (Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank.address wire))

numeric_data_binding nativeAddressLeaf0 : (data.nativeAddress.toList.drop 0).take 32 =
  NumericQueryFrameChecks.window nativeAddressSource 0 32 (by decide +kernel)

theorem nativeAddressSlice0 : (data.nativeAddress.toList.drop 0).take 32 = ((List.ofFn nativeAddressSource).drop 0).take 32 :=
  nativeAddressLeaf0.trans (NumericQueryFrameChecks.window_binding nativeAddressSource 0 32 (by decide +kernel))

numeric_data_binding nativeAddressLeaf32 : (data.nativeAddress.toList.drop 32).take 30 =
  NumericQueryFrameChecks.window nativeAddressSource 32 30 (by decide +kernel)

theorem nativeAddressSlice32 : (data.nativeAddress.toList.drop 32).take 30 = ((List.ofFn nativeAddressSource).drop 32).take 30 :=
  nativeAddressLeaf32.trans (NumericQueryFrameChecks.window_binding nativeAddressSource 32 30 (by decide +kernel))

theorem nativeAddressNode0_62 : (data.nativeAddress.toList.drop 0).take 62 = ((List.ofFn nativeAddressSource).drop 0).take 62 :=
  NumericQueryFrameChecks.merge_bindings data.nativeAddress.toList (List.ofFn nativeAddressSource) 0 32 30 nativeAddressSlice0 nativeAddressSlice32

theorem nativeAddress_fast_binding : data.nativeAddress.toList = (List.ofFn nativeAddressSource) :=
  NumericQueryFrameChecks.complete_binding data.nativeAddress.toList (List.ofFn nativeAddressSource) 62
    (by decide +kernel) List.length_ofFn nativeAddressNode0_62

end Airbender.Compiler.MemoryFrameChecks.JumpBranchCached
