import Airbender.Proofs.GKRProtocol.QueryFrameChecks.KeccakUncached.Data
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.QueryFrameChecks.KeccakUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def returnedAddressSource : Fin 226 → Nat := (fun wire : Fin 226 => AddressUniqueChecks.addressCode (Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.inputBank.address (Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.inputBank.placement (Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank.address wire))))

numeric_data_binding returnedAddressLeaf0 : (data.returnedAddress.drop 0).take 32 =
  NumericQueryFrameChecks.window returnedAddressSource 0 32 (by decide +kernel)

theorem returnedAddressSlice0 : (data.returnedAddress.drop 0).take 32 = ((List.ofFn returnedAddressSource).drop 0).take 32 :=
  returnedAddressLeaf0.trans (NumericQueryFrameChecks.window_binding returnedAddressSource 0 32 (by decide +kernel))

numeric_data_binding returnedAddressLeaf32 : (data.returnedAddress.drop 32).take 32 =
  NumericQueryFrameChecks.window returnedAddressSource 32 32 (by decide +kernel)

theorem returnedAddressSlice32 : (data.returnedAddress.drop 32).take 32 = ((List.ofFn returnedAddressSource).drop 32).take 32 :=
  returnedAddressLeaf32.trans (NumericQueryFrameChecks.window_binding returnedAddressSource 32 32 (by decide +kernel))

numeric_data_binding returnedAddressLeaf64 : (data.returnedAddress.drop 64).take 32 =
  NumericQueryFrameChecks.window returnedAddressSource 64 32 (by decide +kernel)

theorem returnedAddressSlice64 : (data.returnedAddress.drop 64).take 32 = ((List.ofFn returnedAddressSource).drop 64).take 32 :=
  returnedAddressLeaf64.trans (NumericQueryFrameChecks.window_binding returnedAddressSource 64 32 (by decide +kernel))

numeric_data_binding returnedAddressLeaf96 : (data.returnedAddress.drop 96).take 32 =
  NumericQueryFrameChecks.window returnedAddressSource 96 32 (by decide +kernel)

theorem returnedAddressSlice96 : (data.returnedAddress.drop 96).take 32 = ((List.ofFn returnedAddressSource).drop 96).take 32 :=
  returnedAddressLeaf96.trans (NumericQueryFrameChecks.window_binding returnedAddressSource 96 32 (by decide +kernel))

numeric_data_binding returnedAddressLeaf128 : (data.returnedAddress.drop 128).take 32 =
  NumericQueryFrameChecks.window returnedAddressSource 128 32 (by decide +kernel)

theorem returnedAddressSlice128 : (data.returnedAddress.drop 128).take 32 = ((List.ofFn returnedAddressSource).drop 128).take 32 :=
  returnedAddressLeaf128.trans (NumericQueryFrameChecks.window_binding returnedAddressSource 128 32 (by decide +kernel))

numeric_data_binding returnedAddressLeaf160 : (data.returnedAddress.drop 160).take 32 =
  NumericQueryFrameChecks.window returnedAddressSource 160 32 (by decide +kernel)

theorem returnedAddressSlice160 : (data.returnedAddress.drop 160).take 32 = ((List.ofFn returnedAddressSource).drop 160).take 32 :=
  returnedAddressLeaf160.trans (NumericQueryFrameChecks.window_binding returnedAddressSource 160 32 (by decide +kernel))

numeric_data_binding returnedAddressLeaf192 : (data.returnedAddress.drop 192).take 32 =
  NumericQueryFrameChecks.window returnedAddressSource 192 32 (by decide +kernel)

theorem returnedAddressSlice192 : (data.returnedAddress.drop 192).take 32 = ((List.ofFn returnedAddressSource).drop 192).take 32 :=
  returnedAddressLeaf192.trans (NumericQueryFrameChecks.window_binding returnedAddressSource 192 32 (by decide +kernel))

numeric_data_binding returnedAddressLeaf224 : (data.returnedAddress.drop 224).take 2 =
  NumericQueryFrameChecks.window returnedAddressSource 224 2 (by decide +kernel)

theorem returnedAddressSlice224 : (data.returnedAddress.drop 224).take 2 = ((List.ofFn returnedAddressSource).drop 224).take 2 :=
  returnedAddressLeaf224.trans (NumericQueryFrameChecks.window_binding returnedAddressSource 224 2 (by decide +kernel))

theorem returnedAddressNode0_64 : (data.returnedAddress.drop 0).take 64 = ((List.ofFn returnedAddressSource).drop 0).take 64 :=
  NumericQueryFrameChecks.merge_bindings data.returnedAddress (List.ofFn returnedAddressSource) 0 32 32 returnedAddressSlice0 returnedAddressSlice32

theorem returnedAddressNode64_64 : (data.returnedAddress.drop 64).take 64 = ((List.ofFn returnedAddressSource).drop 64).take 64 :=
  NumericQueryFrameChecks.merge_bindings data.returnedAddress (List.ofFn returnedAddressSource) 64 32 32 returnedAddressSlice64 returnedAddressSlice96

theorem returnedAddressNode0_128 : (data.returnedAddress.drop 0).take 128 = ((List.ofFn returnedAddressSource).drop 0).take 128 :=
  NumericQueryFrameChecks.merge_bindings data.returnedAddress (List.ofFn returnedAddressSource) 0 64 64 returnedAddressNode0_64 returnedAddressNode64_64

theorem returnedAddressNode128_64 : (data.returnedAddress.drop 128).take 64 = ((List.ofFn returnedAddressSource).drop 128).take 64 :=
  NumericQueryFrameChecks.merge_bindings data.returnedAddress (List.ofFn returnedAddressSource) 128 32 32 returnedAddressSlice128 returnedAddressSlice160

theorem returnedAddressNode192_34 : (data.returnedAddress.drop 192).take 34 = ((List.ofFn returnedAddressSource).drop 192).take 34 :=
  NumericQueryFrameChecks.merge_bindings data.returnedAddress (List.ofFn returnedAddressSource) 192 32 2 returnedAddressSlice192 returnedAddressSlice224

theorem returnedAddressNode128_98 : (data.returnedAddress.drop 128).take 98 = ((List.ofFn returnedAddressSource).drop 128).take 98 :=
  NumericQueryFrameChecks.merge_bindings data.returnedAddress (List.ofFn returnedAddressSource) 128 64 34 returnedAddressNode128_64 returnedAddressNode192_34

theorem returnedAddressNode0_226 : (data.returnedAddress.drop 0).take 226 = ((List.ofFn returnedAddressSource).drop 0).take 226 :=
  NumericQueryFrameChecks.merge_bindings data.returnedAddress (List.ofFn returnedAddressSource) 0 128 98 returnedAddressNode0_128 returnedAddressNode128_98

theorem returnedAddress_binding : data.returnedAddress = (List.ofFn returnedAddressSource) :=
  NumericQueryFrameChecks.complete_binding data.returnedAddress (List.ofFn returnedAddressSource) 226
    (by decide +kernel) (List.length_ofFn) returnedAddressNode0_226

end Airbender.Compiler.QueryFrameChecks.KeccakUncached
