import Airbender.Proofs.GKRProtocol.MemoryFrameChecks.MulDivUncached.Data
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.MemoryFrameChecks.MulDivUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def inputAddressSource : Fin 76 → Nat := (fun wire : Fin 76 => if wire.val < 71 then AddressUniqueChecks.addressCode (Airbender.Compiler.MemoryNative.MulDivUncached.native.bank.address wire) else AddressUniqueChecks.addressCode (Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.inputBank.address (Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.inputBank.placement (Airbender.Compiler.MemoryNative.MulDivUncached.native.bank.address wire))))

numeric_data_binding inputAddressLeaf0 : (data.inputAddress.toList.drop 0).take 32 =
  NumericQueryFrameChecks.window inputAddressSource 0 32 (by decide +kernel)

theorem inputAddressSlice0 : (data.inputAddress.toList.drop 0).take 32 = ((List.ofFn inputAddressSource).drop 0).take 32 :=
  inputAddressLeaf0.trans (NumericQueryFrameChecks.window_binding inputAddressSource 0 32 (by decide +kernel))

numeric_data_binding inputAddressLeaf32 : (data.inputAddress.toList.drop 32).take 32 =
  NumericQueryFrameChecks.window inputAddressSource 32 32 (by decide +kernel)

theorem inputAddressSlice32 : (data.inputAddress.toList.drop 32).take 32 = ((List.ofFn inputAddressSource).drop 32).take 32 :=
  inputAddressLeaf32.trans (NumericQueryFrameChecks.window_binding inputAddressSource 32 32 (by decide +kernel))

numeric_data_binding inputAddressLeaf64 : (data.inputAddress.toList.drop 64).take 12 =
  NumericQueryFrameChecks.window inputAddressSource 64 12 (by decide +kernel)

theorem inputAddressSlice64 : (data.inputAddress.toList.drop 64).take 12 = ((List.ofFn inputAddressSource).drop 64).take 12 :=
  inputAddressLeaf64.trans (NumericQueryFrameChecks.window_binding inputAddressSource 64 12 (by decide +kernel))

theorem inputAddressNode32_44 : (data.inputAddress.toList.drop 32).take 44 = ((List.ofFn inputAddressSource).drop 32).take 44 :=
  NumericQueryFrameChecks.merge_bindings data.inputAddress.toList (List.ofFn inputAddressSource) 32 32 12 inputAddressSlice32 inputAddressSlice64

theorem inputAddressNode0_76 : (data.inputAddress.toList.drop 0).take 76 = ((List.ofFn inputAddressSource).drop 0).take 76 :=
  NumericQueryFrameChecks.merge_bindings data.inputAddress.toList (List.ofFn inputAddressSource) 0 32 44 inputAddressSlice0 inputAddressNode32_44

theorem inputAddress_fast_binding : data.inputAddress.toList = (List.ofFn inputAddressSource) :=
  NumericQueryFrameChecks.complete_binding data.inputAddress.toList (List.ofFn inputAddressSource) 76
    (by decide +kernel) List.length_ofFn inputAddressNode0_76

end Airbender.Compiler.MemoryFrameChecks.MulDivUncached
