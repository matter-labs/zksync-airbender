import Airbender.Proofs.GKRProtocol.MemoryFrameChecks.JumpBranchCached.Data
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.MemoryFrameChecks.JumpBranchCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def fullAddressSource : Fin 62 → Nat := (fun wire : Fin 62 => if wire.val < 55 then AddressUniqueChecks.addressCode (Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank.address wire) else AddressUniqueChecks.addressCode (Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.bank.placement (Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank.address wire))))

numeric_data_binding fullAddressLeaf0 : (data.fullAddress.toList.drop 0).take 32 =
  NumericQueryFrameChecks.window fullAddressSource 0 32 (by decide +kernel)

theorem fullAddressSlice0 : (data.fullAddress.toList.drop 0).take 32 = ((List.ofFn fullAddressSource).drop 0).take 32 :=
  fullAddressLeaf0.trans (NumericQueryFrameChecks.window_binding fullAddressSource 0 32 (by decide +kernel))

numeric_data_binding fullAddressLeaf32 : (data.fullAddress.toList.drop 32).take 30 =
  NumericQueryFrameChecks.window fullAddressSource 32 30 (by decide +kernel)

theorem fullAddressSlice32 : (data.fullAddress.toList.drop 32).take 30 = ((List.ofFn fullAddressSource).drop 32).take 30 :=
  fullAddressLeaf32.trans (NumericQueryFrameChecks.window_binding fullAddressSource 32 30 (by decide +kernel))

theorem fullAddressNode0_62 : (data.fullAddress.toList.drop 0).take 62 = ((List.ofFn fullAddressSource).drop 0).take 62 :=
  NumericQueryFrameChecks.merge_bindings data.fullAddress.toList (List.ofFn fullAddressSource) 0 32 30 fullAddressSlice0 fullAddressSlice32

theorem fullAddress_fast_binding : data.fullAddress.toList = (List.ofFn fullAddressSource) :=
  NumericQueryFrameChecks.complete_binding data.fullAddress.toList (List.ofFn fullAddressSource) 62
    (by decide +kernel) List.length_ofFn fullAddressNode0_62

end Airbender.Compiler.MemoryFrameChecks.JumpBranchCached
