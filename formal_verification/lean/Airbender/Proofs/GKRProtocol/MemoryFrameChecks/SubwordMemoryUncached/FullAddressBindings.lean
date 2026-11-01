import Airbender.Proofs.GKRProtocol.MemoryFrameChecks.SubwordMemoryUncached.Data
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.MemoryFrameChecks.SubwordMemoryUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def fullAddressSource : Fin 72 → Nat := (fun wire : Fin 72 => if wire.val < 68 then AddressUniqueChecks.addressCode (Airbender.Compiler.MemoryNative.SubwordMemoryUncached.native.bank.address wire) else AddressUniqueChecks.addressCode (Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.bank.address (Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.bank.placement (Airbender.Compiler.MemoryNative.SubwordMemoryUncached.native.bank.address wire))))

numeric_data_binding fullAddressLeaf0 : (data.fullAddress.toList.drop 0).take 32 =
  NumericQueryFrameChecks.window fullAddressSource 0 32 (by decide +kernel)

theorem fullAddressSlice0 : (data.fullAddress.toList.drop 0).take 32 = ((List.ofFn fullAddressSource).drop 0).take 32 :=
  fullAddressLeaf0.trans (NumericQueryFrameChecks.window_binding fullAddressSource 0 32 (by decide +kernel))

numeric_data_binding fullAddressLeaf32 : (data.fullAddress.toList.drop 32).take 32 =
  NumericQueryFrameChecks.window fullAddressSource 32 32 (by decide +kernel)

theorem fullAddressSlice32 : (data.fullAddress.toList.drop 32).take 32 = ((List.ofFn fullAddressSource).drop 32).take 32 :=
  fullAddressLeaf32.trans (NumericQueryFrameChecks.window_binding fullAddressSource 32 32 (by decide +kernel))

numeric_data_binding fullAddressLeaf64 : (data.fullAddress.toList.drop 64).take 8 =
  NumericQueryFrameChecks.window fullAddressSource 64 8 (by decide +kernel)

theorem fullAddressSlice64 : (data.fullAddress.toList.drop 64).take 8 = ((List.ofFn fullAddressSource).drop 64).take 8 :=
  fullAddressLeaf64.trans (NumericQueryFrameChecks.window_binding fullAddressSource 64 8 (by decide +kernel))

theorem fullAddressNode32_40 : (data.fullAddress.toList.drop 32).take 40 = ((List.ofFn fullAddressSource).drop 32).take 40 :=
  NumericQueryFrameChecks.merge_bindings data.fullAddress.toList (List.ofFn fullAddressSource) 32 32 8 fullAddressSlice32 fullAddressSlice64

theorem fullAddressNode0_72 : (data.fullAddress.toList.drop 0).take 72 = ((List.ofFn fullAddressSource).drop 0).take 72 :=
  NumericQueryFrameChecks.merge_bindings data.fullAddress.toList (List.ofFn fullAddressSource) 0 32 40 fullAddressSlice0 fullAddressNode32_40

theorem fullAddress_fast_binding : data.fullAddress.toList = (List.ofFn fullAddressSource) :=
  NumericQueryFrameChecks.complete_binding data.fullAddress.toList (List.ofFn fullAddressSource) 72
    (by decide +kernel) List.length_ofFn fullAddressNode0_72

end Airbender.Compiler.MemoryFrameChecks.SubwordMemoryUncached
