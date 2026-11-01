import Airbender.Proofs.GKRProtocol.MemoryFrameChecks.MulDivCached.Data
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.MemoryFrameChecks.MulDivCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def inputAddressSource : Fin 78 → Nat := (fun wire : Fin 78 => if wire.val < 71 then AddressUniqueChecks.addressCode (Airbender.Compiler.MemoryNative.MulDivCached.native.bank.address wire) else AddressUniqueChecks.addressCode (Airbender.Compiler.FullArithmeticNative.MulDivCached.native.inputBank.address (Airbender.Compiler.FullArithmeticNative.MulDivCached.native.inputBank.placement (Airbender.Compiler.MemoryNative.MulDivCached.native.bank.address wire))))

numeric_data_binding inputAddressLeaf0 : (data.inputAddress.toList.drop 0).take 32 =
  NumericQueryFrameChecks.window inputAddressSource 0 32 (by decide +kernel)

theorem inputAddressSlice0 : (data.inputAddress.toList.drop 0).take 32 = ((List.ofFn inputAddressSource).drop 0).take 32 :=
  inputAddressLeaf0.trans (NumericQueryFrameChecks.window_binding inputAddressSource 0 32 (by decide +kernel))

numeric_data_binding inputAddressLeaf32 : (data.inputAddress.toList.drop 32).take 32 =
  NumericQueryFrameChecks.window inputAddressSource 32 32 (by decide +kernel)

theorem inputAddressSlice32 : (data.inputAddress.toList.drop 32).take 32 = ((List.ofFn inputAddressSource).drop 32).take 32 :=
  inputAddressLeaf32.trans (NumericQueryFrameChecks.window_binding inputAddressSource 32 32 (by decide +kernel))

numeric_data_binding inputAddressLeaf64 : (data.inputAddress.toList.drop 64).take 14 =
  NumericQueryFrameChecks.window inputAddressSource 64 14 (by decide +kernel)

theorem inputAddressSlice64 : (data.inputAddress.toList.drop 64).take 14 = ((List.ofFn inputAddressSource).drop 64).take 14 :=
  inputAddressLeaf64.trans (NumericQueryFrameChecks.window_binding inputAddressSource 64 14 (by decide +kernel))

theorem inputAddressNode32_46 : (data.inputAddress.toList.drop 32).take 46 = ((List.ofFn inputAddressSource).drop 32).take 46 :=
  NumericQueryFrameChecks.merge_bindings data.inputAddress.toList (List.ofFn inputAddressSource) 32 32 14 inputAddressSlice32 inputAddressSlice64

theorem inputAddressNode0_78 : (data.inputAddress.toList.drop 0).take 78 = ((List.ofFn inputAddressSource).drop 0).take 78 :=
  NumericQueryFrameChecks.merge_bindings data.inputAddress.toList (List.ofFn inputAddressSource) 0 32 46 inputAddressSlice0 inputAddressNode32_46

theorem inputAddress_fast_binding : data.inputAddress.toList = (List.ofFn inputAddressSource) :=
  NumericQueryFrameChecks.complete_binding data.inputAddress.toList (List.ofFn inputAddressSource) 78
    (by decide +kernel) List.length_ofFn inputAddressNode0_78

end Airbender.Compiler.MemoryFrameChecks.MulDivCached
