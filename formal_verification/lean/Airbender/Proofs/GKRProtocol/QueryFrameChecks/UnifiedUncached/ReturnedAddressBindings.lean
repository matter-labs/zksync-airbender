import Airbender.Proofs.GKRProtocol.QueryFrameChecks.UnifiedUncached.Data
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.QueryFrameChecks.UnifiedUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def returnedAddressSource : Fin 126 → Nat := (fun wire : Fin 126 => AddressUniqueChecks.addressCode (Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.inputBank.address (Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.inputBank.placement (Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.bank.address wire))))

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

numeric_data_binding returnedAddressLeaf96 : (data.returnedAddress.drop 96).take 30 =
  NumericQueryFrameChecks.window returnedAddressSource 96 30 (by decide +kernel)

theorem returnedAddressSlice96 : (data.returnedAddress.drop 96).take 30 = ((List.ofFn returnedAddressSource).drop 96).take 30 :=
  returnedAddressLeaf96.trans (NumericQueryFrameChecks.window_binding returnedAddressSource 96 30 (by decide +kernel))

theorem returnedAddressNode0_64 : (data.returnedAddress.drop 0).take 64 = ((List.ofFn returnedAddressSource).drop 0).take 64 :=
  NumericQueryFrameChecks.merge_bindings data.returnedAddress (List.ofFn returnedAddressSource) 0 32 32 returnedAddressSlice0 returnedAddressSlice32

theorem returnedAddressNode64_62 : (data.returnedAddress.drop 64).take 62 = ((List.ofFn returnedAddressSource).drop 64).take 62 :=
  NumericQueryFrameChecks.merge_bindings data.returnedAddress (List.ofFn returnedAddressSource) 64 32 30 returnedAddressSlice64 returnedAddressSlice96

theorem returnedAddressNode0_126 : (data.returnedAddress.drop 0).take 126 = ((List.ofFn returnedAddressSource).drop 0).take 126 :=
  NumericQueryFrameChecks.merge_bindings data.returnedAddress (List.ofFn returnedAddressSource) 0 64 62 returnedAddressNode0_64 returnedAddressNode64_62

theorem returnedAddress_binding : data.returnedAddress = (List.ofFn returnedAddressSource) :=
  NumericQueryFrameChecks.complete_binding data.returnedAddress (List.ofFn returnedAddressSource) 126
    (by decide +kernel) (List.length_ofFn) returnedAddressNode0_126

end Airbender.Compiler.QueryFrameChecks.UnifiedUncached
