import Airbender.Proofs.GKRProtocol.QueryFrameChecks.WordMemoryUncached.Data
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.QueryFrameChecks.WordMemoryUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def nativeAddressSource : Fin 50 → Nat := (fun wire : Fin 50 => AddressUniqueChecks.addressCode (Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.bank.address wire))

numeric_data_binding nativeAddressLeaf0 : (data.nativeAddress.drop 0).take 32 =
  NumericQueryFrameChecks.window nativeAddressSource 0 32 (by decide +kernel)

theorem nativeAddressSlice0 : (data.nativeAddress.drop 0).take 32 = ((List.ofFn nativeAddressSource).drop 0).take 32 :=
  nativeAddressLeaf0.trans (NumericQueryFrameChecks.window_binding nativeAddressSource 0 32 (by decide +kernel))

numeric_data_binding nativeAddressLeaf32 : (data.nativeAddress.drop 32).take 18 =
  NumericQueryFrameChecks.window nativeAddressSource 32 18 (by decide +kernel)

theorem nativeAddressSlice32 : (data.nativeAddress.drop 32).take 18 = ((List.ofFn nativeAddressSource).drop 32).take 18 :=
  nativeAddressLeaf32.trans (NumericQueryFrameChecks.window_binding nativeAddressSource 32 18 (by decide +kernel))

theorem nativeAddressNode0_50 : (data.nativeAddress.drop 0).take 50 = ((List.ofFn nativeAddressSource).drop 0).take 50 :=
  NumericQueryFrameChecks.merge_bindings data.nativeAddress (List.ofFn nativeAddressSource) 0 32 18 nativeAddressSlice0 nativeAddressSlice32

theorem nativeAddress_binding : data.nativeAddress = (List.ofFn nativeAddressSource) :=
  NumericQueryFrameChecks.complete_binding data.nativeAddress (List.ofFn nativeAddressSource) 50
    (by decide +kernel) (List.length_ofFn) nativeAddressNode0_50

end Airbender.Compiler.QueryFrameChecks.WordMemoryUncached
