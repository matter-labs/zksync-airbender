import Airbender.Proofs.GKRProtocol.MemoryFrameChecks.SubwordMemoryUncached.Data
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.MemoryFrameChecks.SubwordMemoryUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def inputAddressSource : Fin 72 → Nat := (fun wire : Fin 72 => if wire.val < 68 then AddressUniqueChecks.addressCode (Airbender.Compiler.MemoryNative.SubwordMemoryUncached.native.bank.address wire) else AddressUniqueChecks.addressCode (Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.inputBank.address (Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.inputBank.placement (Airbender.Compiler.MemoryNative.SubwordMemoryUncached.native.bank.address wire))))

numeric_data_binding inputAddressLeaf0 : (data.inputAddress.toList.drop 0).take 32 =
  NumericQueryFrameChecks.window inputAddressSource 0 32 (by decide +kernel)

theorem inputAddressSlice0 : (data.inputAddress.toList.drop 0).take 32 = ((List.ofFn inputAddressSource).drop 0).take 32 :=
  inputAddressLeaf0.trans (NumericQueryFrameChecks.window_binding inputAddressSource 0 32 (by decide +kernel))

numeric_data_binding inputAddressLeaf32 : (data.inputAddress.toList.drop 32).take 32 =
  NumericQueryFrameChecks.window inputAddressSource 32 32 (by decide +kernel)

theorem inputAddressSlice32 : (data.inputAddress.toList.drop 32).take 32 = ((List.ofFn inputAddressSource).drop 32).take 32 :=
  inputAddressLeaf32.trans (NumericQueryFrameChecks.window_binding inputAddressSource 32 32 (by decide +kernel))

numeric_data_binding inputAddressLeaf64 : (data.inputAddress.toList.drop 64).take 8 =
  NumericQueryFrameChecks.window inputAddressSource 64 8 (by decide +kernel)

theorem inputAddressSlice64 : (data.inputAddress.toList.drop 64).take 8 = ((List.ofFn inputAddressSource).drop 64).take 8 :=
  inputAddressLeaf64.trans (NumericQueryFrameChecks.window_binding inputAddressSource 64 8 (by decide +kernel))

theorem inputAddressNode32_40 : (data.inputAddress.toList.drop 32).take 40 = ((List.ofFn inputAddressSource).drop 32).take 40 :=
  NumericQueryFrameChecks.merge_bindings data.inputAddress.toList (List.ofFn inputAddressSource) 32 32 8 inputAddressSlice32 inputAddressSlice64

theorem inputAddressNode0_72 : (data.inputAddress.toList.drop 0).take 72 = ((List.ofFn inputAddressSource).drop 0).take 72 :=
  NumericQueryFrameChecks.merge_bindings data.inputAddress.toList (List.ofFn inputAddressSource) 0 32 40 inputAddressSlice0 inputAddressNode32_40

theorem inputAddress_fast_binding : data.inputAddress.toList = (List.ofFn inputAddressSource) :=
  NumericQueryFrameChecks.complete_binding data.inputAddress.toList (List.ofFn inputAddressSource) 72
    (by decide +kernel) List.length_ofFn inputAddressNode0_72

end Airbender.Compiler.MemoryFrameChecks.SubwordMemoryUncached
