import Airbender.Proofs.GKRProtocol.QueryFrameChecks.ShiftBinopUncached.Data
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.QueryFrameChecks.ShiftBinopUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def returnedAddressSource : Fin 95 → Nat := (fun wire : Fin 95 => AddressUniqueChecks.addressCode (Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.inputBank.address (Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.inputBank.placement (Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank.address wire))))

numeric_data_binding returnedAddressLeaf0 : (data.returnedAddress.drop 0).take 32 =
  NumericQueryFrameChecks.window returnedAddressSource 0 32 (by decide +kernel)

theorem returnedAddressSlice0 : (data.returnedAddress.drop 0).take 32 = ((List.ofFn returnedAddressSource).drop 0).take 32 :=
  returnedAddressLeaf0.trans (NumericQueryFrameChecks.window_binding returnedAddressSource 0 32 (by decide +kernel))

numeric_data_binding returnedAddressLeaf32 : (data.returnedAddress.drop 32).take 32 =
  NumericQueryFrameChecks.window returnedAddressSource 32 32 (by decide +kernel)

theorem returnedAddressSlice32 : (data.returnedAddress.drop 32).take 32 = ((List.ofFn returnedAddressSource).drop 32).take 32 :=
  returnedAddressLeaf32.trans (NumericQueryFrameChecks.window_binding returnedAddressSource 32 32 (by decide +kernel))

numeric_data_binding returnedAddressLeaf64 : (data.returnedAddress.drop 64).take 31 =
  NumericQueryFrameChecks.window returnedAddressSource 64 31 (by decide +kernel)

theorem returnedAddressSlice64 : (data.returnedAddress.drop 64).take 31 = ((List.ofFn returnedAddressSource).drop 64).take 31 :=
  returnedAddressLeaf64.trans (NumericQueryFrameChecks.window_binding returnedAddressSource 64 31 (by decide +kernel))

theorem returnedAddressNode32_63 : (data.returnedAddress.drop 32).take 63 = ((List.ofFn returnedAddressSource).drop 32).take 63 :=
  NumericQueryFrameChecks.merge_bindings data.returnedAddress (List.ofFn returnedAddressSource) 32 32 31 returnedAddressSlice32 returnedAddressSlice64

theorem returnedAddressNode0_95 : (data.returnedAddress.drop 0).take 95 = ((List.ofFn returnedAddressSource).drop 0).take 95 :=
  NumericQueryFrameChecks.merge_bindings data.returnedAddress (List.ofFn returnedAddressSource) 0 32 63 returnedAddressSlice0 returnedAddressNode32_63

theorem returnedAddress_binding : data.returnedAddress = (List.ofFn returnedAddressSource) :=
  NumericQueryFrameChecks.complete_binding data.returnedAddress (List.ofFn returnedAddressSource) 95
    (by decide +kernel) (List.length_ofFn) returnedAddressNode0_95

end Airbender.Compiler.QueryFrameChecks.ShiftBinopUncached
