import Airbender.Proofs.GKRProtocol.MemoryFrameChecks.ShiftBinopUncached.Data
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.MemoryFrameChecks.ShiftBinopUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def inputAddressSource : Fin 103 → Nat := (fun wire : Fin 103 => if wire.val < 98 then AddressUniqueChecks.addressCode (Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.bank.address wire) else AddressUniqueChecks.addressCode (Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.inputBank.address (Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.inputBank.placement (Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.bank.address wire))))

numeric_data_binding inputAddressLeaf0 : (data.inputAddress.toList.drop 0).take 32 =
  NumericQueryFrameChecks.window inputAddressSource 0 32 (by decide +kernel)

theorem inputAddressSlice0 : (data.inputAddress.toList.drop 0).take 32 = ((List.ofFn inputAddressSource).drop 0).take 32 :=
  inputAddressLeaf0.trans (NumericQueryFrameChecks.window_binding inputAddressSource 0 32 (by decide +kernel))

numeric_data_binding inputAddressLeaf32 : (data.inputAddress.toList.drop 32).take 32 =
  NumericQueryFrameChecks.window inputAddressSource 32 32 (by decide +kernel)

theorem inputAddressSlice32 : (data.inputAddress.toList.drop 32).take 32 = ((List.ofFn inputAddressSource).drop 32).take 32 :=
  inputAddressLeaf32.trans (NumericQueryFrameChecks.window_binding inputAddressSource 32 32 (by decide +kernel))

numeric_data_binding inputAddressLeaf64 : (data.inputAddress.toList.drop 64).take 32 =
  NumericQueryFrameChecks.window inputAddressSource 64 32 (by decide +kernel)

theorem inputAddressSlice64 : (data.inputAddress.toList.drop 64).take 32 = ((List.ofFn inputAddressSource).drop 64).take 32 :=
  inputAddressLeaf64.trans (NumericQueryFrameChecks.window_binding inputAddressSource 64 32 (by decide +kernel))

numeric_data_binding inputAddressLeaf96 : (data.inputAddress.toList.drop 96).take 7 =
  NumericQueryFrameChecks.window inputAddressSource 96 7 (by decide +kernel)

theorem inputAddressSlice96 : (data.inputAddress.toList.drop 96).take 7 = ((List.ofFn inputAddressSource).drop 96).take 7 :=
  inputAddressLeaf96.trans (NumericQueryFrameChecks.window_binding inputAddressSource 96 7 (by decide +kernel))

theorem inputAddressNode0_64 : (data.inputAddress.toList.drop 0).take 64 = ((List.ofFn inputAddressSource).drop 0).take 64 :=
  NumericQueryFrameChecks.merge_bindings data.inputAddress.toList (List.ofFn inputAddressSource) 0 32 32 inputAddressSlice0 inputAddressSlice32

theorem inputAddressNode64_39 : (data.inputAddress.toList.drop 64).take 39 = ((List.ofFn inputAddressSource).drop 64).take 39 :=
  NumericQueryFrameChecks.merge_bindings data.inputAddress.toList (List.ofFn inputAddressSource) 64 32 7 inputAddressSlice64 inputAddressSlice96

theorem inputAddressNode0_103 : (data.inputAddress.toList.drop 0).take 103 = ((List.ofFn inputAddressSource).drop 0).take 103 :=
  NumericQueryFrameChecks.merge_bindings data.inputAddress.toList (List.ofFn inputAddressSource) 0 64 39 inputAddressNode0_64 inputAddressNode64_39

theorem inputAddress_fast_binding : data.inputAddress.toList = (List.ofFn inputAddressSource) :=
  NumericQueryFrameChecks.complete_binding data.inputAddress.toList (List.ofFn inputAddressSource) 103
    (by decide +kernel) List.length_ofFn inputAddressNode0_103

end Airbender.Compiler.MemoryFrameChecks.ShiftBinopUncached
