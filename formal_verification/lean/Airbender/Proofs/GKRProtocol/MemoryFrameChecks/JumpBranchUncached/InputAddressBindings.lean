import Airbender.Proofs.GKRProtocol.MemoryFrameChecks.JumpBranchUncached.Data
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.MemoryFrameChecks.JumpBranchUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def inputAddressSource : Fin 60 → Nat := (fun wire : Fin 60 => if wire.val < 55 then AddressUniqueChecks.addressCode (Airbender.Compiler.MemoryNative.JumpBranchUncached.native.bank.address wire) else AddressUniqueChecks.addressCode (Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.inputBank.address (Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.inputBank.placement (Airbender.Compiler.MemoryNative.JumpBranchUncached.native.bank.address wire))))

numeric_data_binding inputAddressLeaf0 : (data.inputAddress.toList.drop 0).take 32 =
  NumericQueryFrameChecks.window inputAddressSource 0 32 (by decide +kernel)

theorem inputAddressSlice0 : (data.inputAddress.toList.drop 0).take 32 = ((List.ofFn inputAddressSource).drop 0).take 32 :=
  inputAddressLeaf0.trans (NumericQueryFrameChecks.window_binding inputAddressSource 0 32 (by decide +kernel))

numeric_data_binding inputAddressLeaf32 : (data.inputAddress.toList.drop 32).take 28 =
  NumericQueryFrameChecks.window inputAddressSource 32 28 (by decide +kernel)

theorem inputAddressSlice32 : (data.inputAddress.toList.drop 32).take 28 = ((List.ofFn inputAddressSource).drop 32).take 28 :=
  inputAddressLeaf32.trans (NumericQueryFrameChecks.window_binding inputAddressSource 32 28 (by decide +kernel))

theorem inputAddressNode0_60 : (data.inputAddress.toList.drop 0).take 60 = ((List.ofFn inputAddressSource).drop 0).take 60 :=
  NumericQueryFrameChecks.merge_bindings data.inputAddress.toList (List.ofFn inputAddressSource) 0 32 28 inputAddressSlice0 inputAddressSlice32

theorem inputAddress_fast_binding : data.inputAddress.toList = (List.ofFn inputAddressSource) :=
  NumericQueryFrameChecks.complete_binding data.inputAddress.toList (List.ofFn inputAddressSource) 60
    (by decide +kernel) List.length_ofFn inputAddressNode0_60

end Airbender.Compiler.MemoryFrameChecks.JumpBranchUncached
