import Airbender.Proofs.GKRProtocol.QueryFrameChecks.MulDivUncached.Data
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.QueryFrameChecks.MulDivUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def nativeAddressSource : Fin 68 → Nat := (fun wire : Fin 68 => AddressUniqueChecks.addressCode (Airbender.Compiler.LookupSourceNative.MulDivUncached.native.bank.address wire))

numeric_data_binding nativeAddressLeaf0 : (data.nativeAddress.drop 0).take 32 =
  NumericQueryFrameChecks.window nativeAddressSource 0 32 (by decide +kernel)

theorem nativeAddressSlice0 : (data.nativeAddress.drop 0).take 32 = ((List.ofFn nativeAddressSource).drop 0).take 32 :=
  nativeAddressLeaf0.trans (NumericQueryFrameChecks.window_binding nativeAddressSource 0 32 (by decide +kernel))

numeric_data_binding nativeAddressLeaf32 : (data.nativeAddress.drop 32).take 32 =
  NumericQueryFrameChecks.window nativeAddressSource 32 32 (by decide +kernel)

theorem nativeAddressSlice32 : (data.nativeAddress.drop 32).take 32 = ((List.ofFn nativeAddressSource).drop 32).take 32 :=
  nativeAddressLeaf32.trans (NumericQueryFrameChecks.window_binding nativeAddressSource 32 32 (by decide +kernel))

numeric_data_binding nativeAddressLeaf64 : (data.nativeAddress.drop 64).take 4 =
  NumericQueryFrameChecks.window nativeAddressSource 64 4 (by decide +kernel)

theorem nativeAddressSlice64 : (data.nativeAddress.drop 64).take 4 = ((List.ofFn nativeAddressSource).drop 64).take 4 :=
  nativeAddressLeaf64.trans (NumericQueryFrameChecks.window_binding nativeAddressSource 64 4 (by decide +kernel))

theorem nativeAddressNode32_36 : (data.nativeAddress.drop 32).take 36 = ((List.ofFn nativeAddressSource).drop 32).take 36 :=
  NumericQueryFrameChecks.merge_bindings data.nativeAddress (List.ofFn nativeAddressSource) 32 32 4 nativeAddressSlice32 nativeAddressSlice64

theorem nativeAddressNode0_68 : (data.nativeAddress.drop 0).take 68 = ((List.ofFn nativeAddressSource).drop 0).take 68 :=
  NumericQueryFrameChecks.merge_bindings data.nativeAddress (List.ofFn nativeAddressSource) 0 32 36 nativeAddressSlice0 nativeAddressNode32_36

theorem nativeAddress_binding : data.nativeAddress = (List.ofFn nativeAddressSource) :=
  NumericQueryFrameChecks.complete_binding data.nativeAddress (List.ofFn nativeAddressSource) 68
    (by decide +kernel) (List.length_ofFn) nativeAddressNode0_68

end Airbender.Compiler.QueryFrameChecks.MulDivUncached
