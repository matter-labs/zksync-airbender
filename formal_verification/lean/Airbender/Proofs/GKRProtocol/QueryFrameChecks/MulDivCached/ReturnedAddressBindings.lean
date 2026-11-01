import Airbender.Proofs.GKRProtocol.QueryFrameChecks.MulDivCached.Data
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.QueryFrameChecks.MulDivCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def returnedAddressSource : Fin 70 → Nat := (fun wire : Fin 70 => AddressUniqueChecks.addressCode (Airbender.Compiler.FullArithmeticNative.MulDivCached.native.inputBank.address (Airbender.Compiler.FullArithmeticNative.MulDivCached.native.inputBank.placement (Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address wire))))

numeric_data_binding returnedAddressLeaf0 : (data.returnedAddress.drop 0).take 32 =
  NumericQueryFrameChecks.window returnedAddressSource 0 32 (by decide +kernel)

theorem returnedAddressSlice0 : (data.returnedAddress.drop 0).take 32 = ((List.ofFn returnedAddressSource).drop 0).take 32 :=
  returnedAddressLeaf0.trans (NumericQueryFrameChecks.window_binding returnedAddressSource 0 32 (by decide +kernel))

numeric_data_binding returnedAddressLeaf32 : (data.returnedAddress.drop 32).take 32 =
  NumericQueryFrameChecks.window returnedAddressSource 32 32 (by decide +kernel)

theorem returnedAddressSlice32 : (data.returnedAddress.drop 32).take 32 = ((List.ofFn returnedAddressSource).drop 32).take 32 :=
  returnedAddressLeaf32.trans (NumericQueryFrameChecks.window_binding returnedAddressSource 32 32 (by decide +kernel))

numeric_data_binding returnedAddressLeaf64 : (data.returnedAddress.drop 64).take 6 =
  NumericQueryFrameChecks.window returnedAddressSource 64 6 (by decide +kernel)

theorem returnedAddressSlice64 : (data.returnedAddress.drop 64).take 6 = ((List.ofFn returnedAddressSource).drop 64).take 6 :=
  returnedAddressLeaf64.trans (NumericQueryFrameChecks.window_binding returnedAddressSource 64 6 (by decide +kernel))

theorem returnedAddressNode32_38 : (data.returnedAddress.drop 32).take 38 = ((List.ofFn returnedAddressSource).drop 32).take 38 :=
  NumericQueryFrameChecks.merge_bindings data.returnedAddress (List.ofFn returnedAddressSource) 32 32 6 returnedAddressSlice32 returnedAddressSlice64

theorem returnedAddressNode0_70 : (data.returnedAddress.drop 0).take 70 = ((List.ofFn returnedAddressSource).drop 0).take 70 :=
  NumericQueryFrameChecks.merge_bindings data.returnedAddress (List.ofFn returnedAddressSource) 0 32 38 returnedAddressSlice0 returnedAddressNode32_38

theorem returnedAddress_binding : data.returnedAddress = (List.ofFn returnedAddressSource) :=
  NumericQueryFrameChecks.complete_binding data.returnedAddress (List.ofFn returnedAddressSource) 70
    (by decide +kernel) (List.length_ofFn) returnedAddressNode0_70

end Airbender.Compiler.QueryFrameChecks.MulDivCached
