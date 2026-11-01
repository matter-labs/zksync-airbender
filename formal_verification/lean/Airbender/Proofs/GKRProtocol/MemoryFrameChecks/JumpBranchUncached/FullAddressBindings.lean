import Airbender.Proofs.GKRProtocol.MemoryFrameChecks.JumpBranchUncached.Data
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.MemoryFrameChecks.JumpBranchUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def fullAddressSource : Fin 60 → Nat := (fun wire : Fin 60 => if wire.val < 55 then AddressUniqueChecks.addressCode (Airbender.Compiler.MemoryNative.JumpBranchUncached.native.bank.address wire) else AddressUniqueChecks.addressCode (Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.bank.address (Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.bank.placement (Airbender.Compiler.MemoryNative.JumpBranchUncached.native.bank.address wire))))

numeric_data_binding fullAddressLeaf0 : (data.fullAddress.toList.drop 0).take 32 =
  NumericQueryFrameChecks.window fullAddressSource 0 32 (by decide +kernel)

theorem fullAddressSlice0 : (data.fullAddress.toList.drop 0).take 32 = ((List.ofFn fullAddressSource).drop 0).take 32 :=
  fullAddressLeaf0.trans (NumericQueryFrameChecks.window_binding fullAddressSource 0 32 (by decide +kernel))

numeric_data_binding fullAddressLeaf32 : (data.fullAddress.toList.drop 32).take 28 =
  NumericQueryFrameChecks.window fullAddressSource 32 28 (by decide +kernel)

theorem fullAddressSlice32 : (data.fullAddress.toList.drop 32).take 28 = ((List.ofFn fullAddressSource).drop 32).take 28 :=
  fullAddressLeaf32.trans (NumericQueryFrameChecks.window_binding fullAddressSource 32 28 (by decide +kernel))

theorem fullAddressNode0_60 : (data.fullAddress.toList.drop 0).take 60 = ((List.ofFn fullAddressSource).drop 0).take 60 :=
  NumericQueryFrameChecks.merge_bindings data.fullAddress.toList (List.ofFn fullAddressSource) 0 32 28 fullAddressSlice0 fullAddressSlice32

theorem fullAddress_fast_binding : data.fullAddress.toList = (List.ofFn fullAddressSource) :=
  NumericQueryFrameChecks.complete_binding data.fullAddress.toList (List.ofFn fullAddressSource) 60
    (by decide +kernel) List.length_ofFn fullAddressNode0_60

end Airbender.Compiler.MemoryFrameChecks.JumpBranchUncached
