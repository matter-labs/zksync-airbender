import Airbender.Proofs.GKRProtocol.QueryFrameChecks.BlakeGCached.Data
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.QueryFrameChecks.BlakeGCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def returnedAddressSource : Fin 87 → Nat := (fun wire : Fin 87 => AddressUniqueChecks.addressCode (Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.inputBank.address (Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.inputBank.placement (Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank.address wire))))

numeric_data_binding returnedAddressLeaf0 : (data.returnedAddress.drop 0).take 32 =
  NumericQueryFrameChecks.window returnedAddressSource 0 32 (by decide +kernel)

theorem returnedAddressSlice0 : (data.returnedAddress.drop 0).take 32 = ((List.ofFn returnedAddressSource).drop 0).take 32 :=
  returnedAddressLeaf0.trans (NumericQueryFrameChecks.window_binding returnedAddressSource 0 32 (by decide +kernel))

numeric_data_binding returnedAddressLeaf32 : (data.returnedAddress.drop 32).take 32 =
  NumericQueryFrameChecks.window returnedAddressSource 32 32 (by decide +kernel)

theorem returnedAddressSlice32 : (data.returnedAddress.drop 32).take 32 = ((List.ofFn returnedAddressSource).drop 32).take 32 :=
  returnedAddressLeaf32.trans (NumericQueryFrameChecks.window_binding returnedAddressSource 32 32 (by decide +kernel))

numeric_data_binding returnedAddressLeaf64 : (data.returnedAddress.drop 64).take 23 =
  NumericQueryFrameChecks.window returnedAddressSource 64 23 (by decide +kernel)

theorem returnedAddressSlice64 : (data.returnedAddress.drop 64).take 23 = ((List.ofFn returnedAddressSource).drop 64).take 23 :=
  returnedAddressLeaf64.trans (NumericQueryFrameChecks.window_binding returnedAddressSource 64 23 (by decide +kernel))

theorem returnedAddressNode32_55 : (data.returnedAddress.drop 32).take 55 = ((List.ofFn returnedAddressSource).drop 32).take 55 :=
  NumericQueryFrameChecks.merge_bindings data.returnedAddress (List.ofFn returnedAddressSource) 32 32 23 returnedAddressSlice32 returnedAddressSlice64

theorem returnedAddressNode0_87 : (data.returnedAddress.drop 0).take 87 = ((List.ofFn returnedAddressSource).drop 0).take 87 :=
  NumericQueryFrameChecks.merge_bindings data.returnedAddress (List.ofFn returnedAddressSource) 0 32 55 returnedAddressSlice0 returnedAddressNode32_55

theorem returnedAddress_binding : data.returnedAddress = (List.ofFn returnedAddressSource) :=
  NumericQueryFrameChecks.complete_binding data.returnedAddress (List.ofFn returnedAddressSource) 87
    (by decide +kernel) (List.length_ofFn) returnedAddressNode0_87

end Airbender.Compiler.QueryFrameChecks.BlakeGCached
