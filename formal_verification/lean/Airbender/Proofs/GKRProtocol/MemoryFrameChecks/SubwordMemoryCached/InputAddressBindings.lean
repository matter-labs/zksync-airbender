import Airbender.Proofs.GKRProtocol.MemoryFrameChecks.SubwordMemoryCached.Data
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.MemoryFrameChecks.SubwordMemoryCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def inputAddressSource : Fin 74 → Nat := (fun wire : Fin 74 => if wire.val < 68 then AddressUniqueChecks.addressCode (Airbender.Compiler.MemoryNative.SubwordMemoryCached.native.bank.address wire) else AddressUniqueChecks.addressCode (Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.inputBank.address (Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.inputBank.placement (Airbender.Compiler.MemoryNative.SubwordMemoryCached.native.bank.address wire))))

numeric_data_binding inputAddressLeaf0 : (data.inputAddress.toList.drop 0).take 32 =
  NumericQueryFrameChecks.window inputAddressSource 0 32 (by decide +kernel)

theorem inputAddressSlice0 : (data.inputAddress.toList.drop 0).take 32 = ((List.ofFn inputAddressSource).drop 0).take 32 :=
  inputAddressLeaf0.trans (NumericQueryFrameChecks.window_binding inputAddressSource 0 32 (by decide +kernel))

numeric_data_binding inputAddressLeaf32 : (data.inputAddress.toList.drop 32).take 32 =
  NumericQueryFrameChecks.window inputAddressSource 32 32 (by decide +kernel)

theorem inputAddressSlice32 : (data.inputAddress.toList.drop 32).take 32 = ((List.ofFn inputAddressSource).drop 32).take 32 :=
  inputAddressLeaf32.trans (NumericQueryFrameChecks.window_binding inputAddressSource 32 32 (by decide +kernel))

numeric_data_binding inputAddressLeaf64 : (data.inputAddress.toList.drop 64).take 10 =
  NumericQueryFrameChecks.window inputAddressSource 64 10 (by decide +kernel)

theorem inputAddressSlice64 : (data.inputAddress.toList.drop 64).take 10 = ((List.ofFn inputAddressSource).drop 64).take 10 :=
  inputAddressLeaf64.trans (NumericQueryFrameChecks.window_binding inputAddressSource 64 10 (by decide +kernel))

theorem inputAddressNode32_42 : (data.inputAddress.toList.drop 32).take 42 = ((List.ofFn inputAddressSource).drop 32).take 42 :=
  NumericQueryFrameChecks.merge_bindings data.inputAddress.toList (List.ofFn inputAddressSource) 32 32 10 inputAddressSlice32 inputAddressSlice64

theorem inputAddressNode0_74 : (data.inputAddress.toList.drop 0).take 74 = ((List.ofFn inputAddressSource).drop 0).take 74 :=
  NumericQueryFrameChecks.merge_bindings data.inputAddress.toList (List.ofFn inputAddressSource) 0 32 42 inputAddressSlice0 inputAddressNode32_42

theorem inputAddress_fast_binding : data.inputAddress.toList = (List.ofFn inputAddressSource) :=
  NumericQueryFrameChecks.complete_binding data.inputAddress.toList (List.ofFn inputAddressSource) 74
    (by decide +kernel) List.length_ofFn inputAddressNode0_74

end Airbender.Compiler.MemoryFrameChecks.SubwordMemoryCached
