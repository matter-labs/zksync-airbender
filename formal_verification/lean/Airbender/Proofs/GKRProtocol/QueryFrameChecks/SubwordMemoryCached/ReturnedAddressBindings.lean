import Airbender.Proofs.GKRProtocol.QueryFrameChecks.SubwordMemoryCached.Data
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.QueryFrameChecks.SubwordMemoryCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def returnedAddressSource : Fin 66 → Nat := (fun wire : Fin 66 => AddressUniqueChecks.addressCode (Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.inputBank.address (Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.inputBank.placement (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address wire))))

numeric_data_binding returnedAddressLeaf0 : (data.returnedAddress.drop 0).take 32 =
  NumericQueryFrameChecks.window returnedAddressSource 0 32 (by decide +kernel)

theorem returnedAddressSlice0 : (data.returnedAddress.drop 0).take 32 = ((List.ofFn returnedAddressSource).drop 0).take 32 :=
  returnedAddressLeaf0.trans (NumericQueryFrameChecks.window_binding returnedAddressSource 0 32 (by decide +kernel))

numeric_data_binding returnedAddressLeaf32 : (data.returnedAddress.drop 32).take 32 =
  NumericQueryFrameChecks.window returnedAddressSource 32 32 (by decide +kernel)

theorem returnedAddressSlice32 : (data.returnedAddress.drop 32).take 32 = ((List.ofFn returnedAddressSource).drop 32).take 32 :=
  returnedAddressLeaf32.trans (NumericQueryFrameChecks.window_binding returnedAddressSource 32 32 (by decide +kernel))

numeric_data_binding returnedAddressLeaf64 : (data.returnedAddress.drop 64).take 2 =
  NumericQueryFrameChecks.window returnedAddressSource 64 2 (by decide +kernel)

theorem returnedAddressSlice64 : (data.returnedAddress.drop 64).take 2 = ((List.ofFn returnedAddressSource).drop 64).take 2 :=
  returnedAddressLeaf64.trans (NumericQueryFrameChecks.window_binding returnedAddressSource 64 2 (by decide +kernel))

theorem returnedAddressNode32_34 : (data.returnedAddress.drop 32).take 34 = ((List.ofFn returnedAddressSource).drop 32).take 34 :=
  NumericQueryFrameChecks.merge_bindings data.returnedAddress (List.ofFn returnedAddressSource) 32 32 2 returnedAddressSlice32 returnedAddressSlice64

theorem returnedAddressNode0_66 : (data.returnedAddress.drop 0).take 66 = ((List.ofFn returnedAddressSource).drop 0).take 66 :=
  NumericQueryFrameChecks.merge_bindings data.returnedAddress (List.ofFn returnedAddressSource) 0 32 34 returnedAddressSlice0 returnedAddressNode32_34

theorem returnedAddress_binding : data.returnedAddress = (List.ofFn returnedAddressSource) :=
  NumericQueryFrameChecks.complete_binding data.returnedAddress (List.ofFn returnedAddressSource) 66
    (by decide +kernel) (List.length_ofFn) returnedAddressNode0_66

end Airbender.Compiler.QueryFrameChecks.SubwordMemoryCached
