import Airbender.Proofs.GKRProtocol.QueryFrameChecks.BigintCached.Data
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.QueryFrameChecks.BigintCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def returnedAddressSource : Fin 222 → Nat := (fun wire : Fin 222 => AddressUniqueChecks.addressCode (Airbender.Compiler.FullArithmeticNative.BigintCached.native.inputBank.address (Airbender.Compiler.FullArithmeticNative.BigintCached.native.inputBank.placement (Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.address wire))))

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

numeric_data_binding returnedAddressLeaf192 : (data.returnedAddress.drop 192).take 30 =
  NumericQueryFrameChecks.window returnedAddressSource 192 30 (by decide +kernel)

theorem returnedAddressSlice192 : (data.returnedAddress.drop 192).take 30 = ((List.ofFn returnedAddressSource).drop 192).take 30 :=
  returnedAddressLeaf192.trans (NumericQueryFrameChecks.window_binding returnedAddressSource 192 30 (by decide +kernel))

theorem returnedAddressNode32_64 : (data.returnedAddress.drop 32).take 64 = ((List.ofFn returnedAddressSource).drop 32).take 64 :=
  NumericQueryFrameChecks.merge_bindings data.returnedAddress (List.ofFn returnedAddressSource) 32 32 32 returnedAddressSlice32 returnedAddressSlice64

theorem returnedAddressNode0_96 : (data.returnedAddress.drop 0).take 96 = ((List.ofFn returnedAddressSource).drop 0).take 96 :=
  NumericQueryFrameChecks.merge_bindings data.returnedAddress (List.ofFn returnedAddressSource) 0 32 64 returnedAddressSlice0 returnedAddressNode32_64

theorem returnedAddressNode96_64 : (data.returnedAddress.drop 96).take 64 = ((List.ofFn returnedAddressSource).drop 96).take 64 :=
  NumericQueryFrameChecks.merge_bindings data.returnedAddress (List.ofFn returnedAddressSource) 96 32 32 returnedAddressSlice96 returnedAddressSlice128

theorem returnedAddressNode160_62 : (data.returnedAddress.drop 160).take 62 = ((List.ofFn returnedAddressSource).drop 160).take 62 :=
  NumericQueryFrameChecks.merge_bindings data.returnedAddress (List.ofFn returnedAddressSource) 160 32 30 returnedAddressSlice160 returnedAddressSlice192

theorem returnedAddressNode96_126 : (data.returnedAddress.drop 96).take 126 = ((List.ofFn returnedAddressSource).drop 96).take 126 :=
  NumericQueryFrameChecks.merge_bindings data.returnedAddress (List.ofFn returnedAddressSource) 96 64 62 returnedAddressNode96_64 returnedAddressNode160_62

theorem returnedAddressNode0_222 : (data.returnedAddress.drop 0).take 222 = ((List.ofFn returnedAddressSource).drop 0).take 222 :=
  NumericQueryFrameChecks.merge_bindings data.returnedAddress (List.ofFn returnedAddressSource) 0 96 126 returnedAddressNode0_96 returnedAddressNode96_126

theorem returnedAddress_binding : data.returnedAddress = (List.ofFn returnedAddressSource) :=
  NumericQueryFrameChecks.complete_binding data.returnedAddress (List.ofFn returnedAddressSource) 222
    (by decide +kernel) (List.length_ofFn) returnedAddressNode0_222

end Airbender.Compiler.QueryFrameChecks.BigintCached
