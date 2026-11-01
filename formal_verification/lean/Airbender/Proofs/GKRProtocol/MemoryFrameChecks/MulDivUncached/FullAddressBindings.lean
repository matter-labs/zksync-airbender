import Airbender.Proofs.GKRProtocol.MemoryFrameChecks.MulDivUncached.Data
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.MemoryFrameChecks.MulDivUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def fullAddressSource : Fin 76 → Nat := (fun wire : Fin 76 => if wire.val < 71 then AddressUniqueChecks.addressCode (Airbender.Compiler.MemoryNative.MulDivUncached.native.bank.address wire) else AddressUniqueChecks.addressCode (Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.bank.address (Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.bank.placement (Airbender.Compiler.MemoryNative.MulDivUncached.native.bank.address wire))))

numeric_data_binding fullAddressLeaf0 : (data.fullAddress.toList.drop 0).take 32 =
  NumericQueryFrameChecks.window fullAddressSource 0 32 (by decide +kernel)

theorem fullAddressSlice0 : (data.fullAddress.toList.drop 0).take 32 = ((List.ofFn fullAddressSource).drop 0).take 32 :=
  fullAddressLeaf0.trans (NumericQueryFrameChecks.window_binding fullAddressSource 0 32 (by decide +kernel))

numeric_data_binding fullAddressLeaf32 : (data.fullAddress.toList.drop 32).take 32 =
  NumericQueryFrameChecks.window fullAddressSource 32 32 (by decide +kernel)

theorem fullAddressSlice32 : (data.fullAddress.toList.drop 32).take 32 = ((List.ofFn fullAddressSource).drop 32).take 32 :=
  fullAddressLeaf32.trans (NumericQueryFrameChecks.window_binding fullAddressSource 32 32 (by decide +kernel))

numeric_data_binding fullAddressLeaf64 : (data.fullAddress.toList.drop 64).take 12 =
  NumericQueryFrameChecks.window fullAddressSource 64 12 (by decide +kernel)

theorem fullAddressSlice64 : (data.fullAddress.toList.drop 64).take 12 = ((List.ofFn fullAddressSource).drop 64).take 12 :=
  fullAddressLeaf64.trans (NumericQueryFrameChecks.window_binding fullAddressSource 64 12 (by decide +kernel))

theorem fullAddressNode32_44 : (data.fullAddress.toList.drop 32).take 44 = ((List.ofFn fullAddressSource).drop 32).take 44 :=
  NumericQueryFrameChecks.merge_bindings data.fullAddress.toList (List.ofFn fullAddressSource) 32 32 12 fullAddressSlice32 fullAddressSlice64

theorem fullAddressNode0_76 : (data.fullAddress.toList.drop 0).take 76 = ((List.ofFn fullAddressSource).drop 0).take 76 :=
  NumericQueryFrameChecks.merge_bindings data.fullAddress.toList (List.ofFn fullAddressSource) 0 32 44 fullAddressSlice0 fullAddressNode32_44

theorem fullAddress_fast_binding : data.fullAddress.toList = (List.ofFn fullAddressSource) :=
  NumericQueryFrameChecks.complete_binding data.fullAddress.toList (List.ofFn fullAddressSource) 76
    (by decide +kernel) List.length_ofFn fullAddressNode0_76

end Airbender.Compiler.MemoryFrameChecks.MulDivUncached
