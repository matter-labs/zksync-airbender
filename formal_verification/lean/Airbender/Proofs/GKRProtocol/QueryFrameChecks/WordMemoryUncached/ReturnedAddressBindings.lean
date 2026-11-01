import Airbender.Proofs.GKRProtocol.QueryFrameChecks.WordMemoryUncached.Data
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.QueryFrameChecks.WordMemoryUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def returnedAddressSource : Fin 50 → Nat := (fun wire : Fin 50 => AddressUniqueChecks.addressCode (Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.inputBank.address (Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.inputBank.placement (Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.bank.address wire))))

numeric_data_binding returnedAddressLeaf0 : (data.returnedAddress.drop 0).take 32 =
  NumericQueryFrameChecks.window returnedAddressSource 0 32 (by decide +kernel)

theorem returnedAddressSlice0 : (data.returnedAddress.drop 0).take 32 = ((List.ofFn returnedAddressSource).drop 0).take 32 :=
  returnedAddressLeaf0.trans (NumericQueryFrameChecks.window_binding returnedAddressSource 0 32 (by decide +kernel))

numeric_data_binding returnedAddressLeaf32 : (data.returnedAddress.drop 32).take 18 =
  NumericQueryFrameChecks.window returnedAddressSource 32 18 (by decide +kernel)

theorem returnedAddressSlice32 : (data.returnedAddress.drop 32).take 18 = ((List.ofFn returnedAddressSource).drop 32).take 18 :=
  returnedAddressLeaf32.trans (NumericQueryFrameChecks.window_binding returnedAddressSource 32 18 (by decide +kernel))

theorem returnedAddressNode0_50 : (data.returnedAddress.drop 0).take 50 = ((List.ofFn returnedAddressSource).drop 0).take 50 :=
  NumericQueryFrameChecks.merge_bindings data.returnedAddress (List.ofFn returnedAddressSource) 0 32 18 returnedAddressSlice0 returnedAddressSlice32

theorem returnedAddress_binding : data.returnedAddress = (List.ofFn returnedAddressSource) :=
  NumericQueryFrameChecks.complete_binding data.returnedAddress (List.ofFn returnedAddressSource) 50
    (by decide +kernel) (List.length_ofFn) returnedAddressNode0_50

end Airbender.Compiler.QueryFrameChecks.WordMemoryUncached
