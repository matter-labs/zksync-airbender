import Airbender.Proofs.GKRProtocol.QueryFrameChecks.MulDivUncached.Data
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.QueryFrameChecks.MulDivUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def returnedAddressSource : Fin 68 → Nat := (fun wire : Fin 68 => AddressUniqueChecks.addressCode (Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.inputBank.address (Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.inputBank.placement (Airbender.Compiler.LookupSourceNative.MulDivUncached.native.bank.address wire))))

numeric_data_binding returnedAddressLeaf0 : (data.returnedAddress.drop 0).take 32 =
  NumericQueryFrameChecks.window returnedAddressSource 0 32 (by decide +kernel)

theorem returnedAddressSlice0 : (data.returnedAddress.drop 0).take 32 = ((List.ofFn returnedAddressSource).drop 0).take 32 :=
  returnedAddressLeaf0.trans (NumericQueryFrameChecks.window_binding returnedAddressSource 0 32 (by decide +kernel))

numeric_data_binding returnedAddressLeaf32 : (data.returnedAddress.drop 32).take 32 =
  NumericQueryFrameChecks.window returnedAddressSource 32 32 (by decide +kernel)

theorem returnedAddressSlice32 : (data.returnedAddress.drop 32).take 32 = ((List.ofFn returnedAddressSource).drop 32).take 32 :=
  returnedAddressLeaf32.trans (NumericQueryFrameChecks.window_binding returnedAddressSource 32 32 (by decide +kernel))

numeric_data_binding returnedAddressLeaf64 : (data.returnedAddress.drop 64).take 4 =
  NumericQueryFrameChecks.window returnedAddressSource 64 4 (by decide +kernel)

theorem returnedAddressSlice64 : (data.returnedAddress.drop 64).take 4 = ((List.ofFn returnedAddressSource).drop 64).take 4 :=
  returnedAddressLeaf64.trans (NumericQueryFrameChecks.window_binding returnedAddressSource 64 4 (by decide +kernel))

theorem returnedAddressNode32_36 : (data.returnedAddress.drop 32).take 36 = ((List.ofFn returnedAddressSource).drop 32).take 36 :=
  NumericQueryFrameChecks.merge_bindings data.returnedAddress (List.ofFn returnedAddressSource) 32 32 4 returnedAddressSlice32 returnedAddressSlice64

theorem returnedAddressNode0_68 : (data.returnedAddress.drop 0).take 68 = ((List.ofFn returnedAddressSource).drop 0).take 68 :=
  NumericQueryFrameChecks.merge_bindings data.returnedAddress (List.ofFn returnedAddressSource) 0 32 36 returnedAddressSlice0 returnedAddressNode32_36

theorem returnedAddress_binding : data.returnedAddress = (List.ofFn returnedAddressSource) :=
  NumericQueryFrameChecks.complete_binding data.returnedAddress (List.ofFn returnedAddressSource) 68
    (by decide +kernel) (List.length_ofFn) returnedAddressNode0_68

end Airbender.Compiler.QueryFrameChecks.MulDivUncached
