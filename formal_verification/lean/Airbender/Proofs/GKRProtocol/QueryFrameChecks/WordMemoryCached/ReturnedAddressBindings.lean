import Airbender.Proofs.GKRProtocol.QueryFrameChecks.WordMemoryCached.Data
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.QueryFrameChecks.WordMemoryCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def returnedAddressSource : Fin 52 → Nat := (fun wire : Fin 52 => AddressUniqueChecks.addressCode (Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.inputBank.address (Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.inputBank.placement (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.address wire))))

numeric_data_binding returnedAddressLeaf0 : (data.returnedAddress.drop 0).take 32 =
  NumericQueryFrameChecks.window returnedAddressSource 0 32 (by decide +kernel)

theorem returnedAddressSlice0 : (data.returnedAddress.drop 0).take 32 = ((List.ofFn returnedAddressSource).drop 0).take 32 :=
  returnedAddressLeaf0.trans (NumericQueryFrameChecks.window_binding returnedAddressSource 0 32 (by decide +kernel))

numeric_data_binding returnedAddressLeaf32 : (data.returnedAddress.drop 32).take 20 =
  NumericQueryFrameChecks.window returnedAddressSource 32 20 (by decide +kernel)

theorem returnedAddressSlice32 : (data.returnedAddress.drop 32).take 20 = ((List.ofFn returnedAddressSource).drop 32).take 20 :=
  returnedAddressLeaf32.trans (NumericQueryFrameChecks.window_binding returnedAddressSource 32 20 (by decide +kernel))

theorem returnedAddressNode0_52 : (data.returnedAddress.drop 0).take 52 = ((List.ofFn returnedAddressSource).drop 0).take 52 :=
  NumericQueryFrameChecks.merge_bindings data.returnedAddress (List.ofFn returnedAddressSource) 0 32 20 returnedAddressSlice0 returnedAddressSlice32

theorem returnedAddress_binding : data.returnedAddress = (List.ofFn returnedAddressSource) :=
  NumericQueryFrameChecks.complete_binding data.returnedAddress (List.ofFn returnedAddressSource) 52
    (by decide +kernel) (List.length_ofFn) returnedAddressNode0_52

end Airbender.Compiler.QueryFrameChecks.WordMemoryCached
