import Airbender.Proofs.GKRProtocol.MemoryFrameChecks.JumpBranchCached.Data
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.MemoryFrameChecks.JumpBranchCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def inputAddressSource : Fin 62 → Nat := (fun wire : Fin 62 => if wire.val < 55 then AddressUniqueChecks.addressCode (Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank.address wire) else AddressUniqueChecks.addressCode (Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.inputBank.address (Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.inputBank.placement (Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank.address wire))))

numeric_data_binding inputAddressLeaf0 : (data.inputAddress.toList.drop 0).take 32 =
  NumericQueryFrameChecks.window inputAddressSource 0 32 (by decide +kernel)

theorem inputAddressSlice0 : (data.inputAddress.toList.drop 0).take 32 = ((List.ofFn inputAddressSource).drop 0).take 32 :=
  inputAddressLeaf0.trans (NumericQueryFrameChecks.window_binding inputAddressSource 0 32 (by decide +kernel))

numeric_data_binding inputAddressLeaf32 : (data.inputAddress.toList.drop 32).take 30 =
  NumericQueryFrameChecks.window inputAddressSource 32 30 (by decide +kernel)

theorem inputAddressSlice32 : (data.inputAddress.toList.drop 32).take 30 = ((List.ofFn inputAddressSource).drop 32).take 30 :=
  inputAddressLeaf32.trans (NumericQueryFrameChecks.window_binding inputAddressSource 32 30 (by decide +kernel))

theorem inputAddressNode0_62 : (data.inputAddress.toList.drop 0).take 62 = ((List.ofFn inputAddressSource).drop 0).take 62 :=
  NumericQueryFrameChecks.merge_bindings data.inputAddress.toList (List.ofFn inputAddressSource) 0 32 30 inputAddressSlice0 inputAddressSlice32

theorem inputAddress_fast_binding : data.inputAddress.toList = (List.ofFn inputAddressSource) :=
  NumericQueryFrameChecks.complete_binding data.inputAddress.toList (List.ofFn inputAddressSource) 62
    (by decide +kernel) List.length_ofFn inputAddressNode0_62

end Airbender.Compiler.MemoryFrameChecks.JumpBranchCached
