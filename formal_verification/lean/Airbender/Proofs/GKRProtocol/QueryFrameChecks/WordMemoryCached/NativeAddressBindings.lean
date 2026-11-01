import Airbender.Proofs.GKRProtocol.QueryFrameChecks.WordMemoryCached.Data
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.QueryFrameChecks.WordMemoryCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def nativeAddressSource : Fin 52 → Nat := (fun wire : Fin 52 => AddressUniqueChecks.addressCode (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.address wire))

numeric_data_binding nativeAddressLeaf0 : (data.nativeAddress.drop 0).take 32 =
  NumericQueryFrameChecks.window nativeAddressSource 0 32 (by decide +kernel)

theorem nativeAddressSlice0 : (data.nativeAddress.drop 0).take 32 = ((List.ofFn nativeAddressSource).drop 0).take 32 :=
  nativeAddressLeaf0.trans (NumericQueryFrameChecks.window_binding nativeAddressSource 0 32 (by decide +kernel))

numeric_data_binding nativeAddressLeaf32 : (data.nativeAddress.drop 32).take 20 =
  NumericQueryFrameChecks.window nativeAddressSource 32 20 (by decide +kernel)

theorem nativeAddressSlice32 : (data.nativeAddress.drop 32).take 20 = ((List.ofFn nativeAddressSource).drop 32).take 20 :=
  nativeAddressLeaf32.trans (NumericQueryFrameChecks.window_binding nativeAddressSource 32 20 (by decide +kernel))

theorem nativeAddressNode0_52 : (data.nativeAddress.drop 0).take 52 = ((List.ofFn nativeAddressSource).drop 0).take 52 :=
  NumericQueryFrameChecks.merge_bindings data.nativeAddress (List.ofFn nativeAddressSource) 0 32 20 nativeAddressSlice0 nativeAddressSlice32

theorem nativeAddress_binding : data.nativeAddress = (List.ofFn nativeAddressSource) :=
  NumericQueryFrameChecks.complete_binding data.nativeAddress (List.ofFn nativeAddressSource) 52
    (by decide +kernel) (List.length_ofFn) nativeAddressNode0_52

end Airbender.Compiler.QueryFrameChecks.WordMemoryCached
