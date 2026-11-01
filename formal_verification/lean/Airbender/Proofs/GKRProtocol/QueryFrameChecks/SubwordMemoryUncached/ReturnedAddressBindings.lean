import Airbender.Proofs.GKRProtocol.QueryFrameChecks.SubwordMemoryUncached.Data
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.QueryFrameChecks.SubwordMemoryUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def returnedAddressSource : Fin 64 → Nat := (fun wire : Fin 64 => AddressUniqueChecks.addressCode (Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.inputBank.address (Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.inputBank.placement (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.address wire))))

numeric_data_binding returnedAddressLeaf0 : (data.returnedAddress.drop 0).take 32 =
  NumericQueryFrameChecks.window returnedAddressSource 0 32 (by decide +kernel)

theorem returnedAddressSlice0 : (data.returnedAddress.drop 0).take 32 = ((List.ofFn returnedAddressSource).drop 0).take 32 :=
  returnedAddressLeaf0.trans (NumericQueryFrameChecks.window_binding returnedAddressSource 0 32 (by decide +kernel))

numeric_data_binding returnedAddressLeaf32 : (data.returnedAddress.drop 32).take 32 =
  NumericQueryFrameChecks.window returnedAddressSource 32 32 (by decide +kernel)

theorem returnedAddressSlice32 : (data.returnedAddress.drop 32).take 32 = ((List.ofFn returnedAddressSource).drop 32).take 32 :=
  returnedAddressLeaf32.trans (NumericQueryFrameChecks.window_binding returnedAddressSource 32 32 (by decide +kernel))

theorem returnedAddressNode0_64 : (data.returnedAddress.drop 0).take 64 = ((List.ofFn returnedAddressSource).drop 0).take 64 :=
  NumericQueryFrameChecks.merge_bindings data.returnedAddress (List.ofFn returnedAddressSource) 0 32 32 returnedAddressSlice0 returnedAddressSlice32

theorem returnedAddress_binding : data.returnedAddress = (List.ofFn returnedAddressSource) :=
  NumericQueryFrameChecks.complete_binding data.returnedAddress (List.ofFn returnedAddressSource) 64
    (by decide +kernel) (List.length_ofFn) returnedAddressNode0_64

end Airbender.Compiler.QueryFrameChecks.SubwordMemoryUncached
