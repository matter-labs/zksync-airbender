import Airbender.Proofs.GKRProtocol.MemoryFrameChecks.UnifiedCached.Data
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.MemoryFrameChecks.UnifiedCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def inputAddressSource : Fin 144 → Nat := (fun wire : Fin 144 => if wire.val < 137 then AddressUniqueChecks.addressCode (Airbender.Compiler.MemoryNative.UnifiedCached.native.bank.address wire) else AddressUniqueChecks.addressCode (Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.inputBank.address (Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.inputBank.placement (Airbender.Compiler.MemoryNative.UnifiedCached.native.bank.address wire))))

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

numeric_data_binding inputAddressLeaf96 : (data.inputAddress.toList.drop 96).take 32 =
  NumericQueryFrameChecks.window inputAddressSource 96 32 (by decide +kernel)

theorem inputAddressSlice96 : (data.inputAddress.toList.drop 96).take 32 = ((List.ofFn inputAddressSource).drop 96).take 32 :=
  inputAddressLeaf96.trans (NumericQueryFrameChecks.window_binding inputAddressSource 96 32 (by decide +kernel))

numeric_data_binding inputAddressLeaf128 : (data.inputAddress.toList.drop 128).take 16 =
  NumericQueryFrameChecks.window inputAddressSource 128 16 (by decide +kernel)

theorem inputAddressSlice128 : (data.inputAddress.toList.drop 128).take 16 = ((List.ofFn inputAddressSource).drop 128).take 16 :=
  inputAddressLeaf128.trans (NumericQueryFrameChecks.window_binding inputAddressSource 128 16 (by decide +kernel))

theorem inputAddressNode0_64 : (data.inputAddress.toList.drop 0).take 64 = ((List.ofFn inputAddressSource).drop 0).take 64 :=
  NumericQueryFrameChecks.merge_bindings data.inputAddress.toList (List.ofFn inputAddressSource) 0 32 32 inputAddressSlice0 inputAddressSlice32

theorem inputAddressNode96_48 : (data.inputAddress.toList.drop 96).take 48 = ((List.ofFn inputAddressSource).drop 96).take 48 :=
  NumericQueryFrameChecks.merge_bindings data.inputAddress.toList (List.ofFn inputAddressSource) 96 32 16 inputAddressSlice96 inputAddressSlice128

theorem inputAddressNode64_80 : (data.inputAddress.toList.drop 64).take 80 = ((List.ofFn inputAddressSource).drop 64).take 80 :=
  NumericQueryFrameChecks.merge_bindings data.inputAddress.toList (List.ofFn inputAddressSource) 64 32 48 inputAddressSlice64 inputAddressNode96_48

theorem inputAddressNode0_144 : (data.inputAddress.toList.drop 0).take 144 = ((List.ofFn inputAddressSource).drop 0).take 144 :=
  NumericQueryFrameChecks.merge_bindings data.inputAddress.toList (List.ofFn inputAddressSource) 0 64 80 inputAddressNode0_64 inputAddressNode64_80

theorem inputAddress_fast_binding : data.inputAddress.toList = (List.ofFn inputAddressSource) :=
  NumericQueryFrameChecks.complete_binding data.inputAddress.toList (List.ofFn inputAddressSource) 144
    (by decide +kernel) List.length_ofFn inputAddressNode0_144

end Airbender.Compiler.MemoryFrameChecks.UnifiedCached
