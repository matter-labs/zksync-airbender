import Airbender.Proofs.GKRProtocol.QueryFrameChecks.JumpBranchCached.Data
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.QueryFrameChecks.JumpBranchCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def returnedAddressSource : Fin 54 → Nat := (fun wire : Fin 54 => AddressUniqueChecks.addressCode (Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.inputBank.address (Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.inputBank.placement (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.bank.address wire))))

numeric_data_binding returnedAddressLeaf0 : (data.returnedAddress.drop 0).take 32 =
  NumericQueryFrameChecks.window returnedAddressSource 0 32 (by decide +kernel)

theorem returnedAddressSlice0 : (data.returnedAddress.drop 0).take 32 = ((List.ofFn returnedAddressSource).drop 0).take 32 :=
  returnedAddressLeaf0.trans (NumericQueryFrameChecks.window_binding returnedAddressSource 0 32 (by decide +kernel))

numeric_data_binding returnedAddressLeaf32 : (data.returnedAddress.drop 32).take 22 =
  NumericQueryFrameChecks.window returnedAddressSource 32 22 (by decide +kernel)

theorem returnedAddressSlice32 : (data.returnedAddress.drop 32).take 22 = ((List.ofFn returnedAddressSource).drop 32).take 22 :=
  returnedAddressLeaf32.trans (NumericQueryFrameChecks.window_binding returnedAddressSource 32 22 (by decide +kernel))

theorem returnedAddressNode0_54 : (data.returnedAddress.drop 0).take 54 = ((List.ofFn returnedAddressSource).drop 0).take 54 :=
  NumericQueryFrameChecks.merge_bindings data.returnedAddress (List.ofFn returnedAddressSource) 0 32 22 returnedAddressSlice0 returnedAddressSlice32

theorem returnedAddress_binding : data.returnedAddress = (List.ofFn returnedAddressSource) :=
  NumericQueryFrameChecks.complete_binding data.returnedAddress (List.ofFn returnedAddressSource) 54
    (by decide +kernel) (List.length_ofFn) returnedAddressNode0_54

end Airbender.Compiler.QueryFrameChecks.JumpBranchCached
