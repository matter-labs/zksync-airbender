import Airbender.Proofs.GKRProtocol.MemoryFrameChecks.ShiftBinopUncached.Data
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.MemoryFrameChecks.ShiftBinopUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def placementSource : Fin 103 → Nat := (fun wire : Fin 103 => if wire.val < 98 then wire.val else (Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.inputBank.placement (Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.bank.address wire)).val)

numeric_data_binding placementLeaf0 : (data.placement.toList.drop 0).take 32 =
  NumericQueryFrameChecks.window placementSource 0 32 (by decide +kernel)

theorem placementSlice0 : (data.placement.toList.drop 0).take 32 = ((List.ofFn placementSource).drop 0).take 32 :=
  placementLeaf0.trans (NumericQueryFrameChecks.window_binding placementSource 0 32 (by decide +kernel))

numeric_data_binding placementLeaf32 : (data.placement.toList.drop 32).take 32 =
  NumericQueryFrameChecks.window placementSource 32 32 (by decide +kernel)

theorem placementSlice32 : (data.placement.toList.drop 32).take 32 = ((List.ofFn placementSource).drop 32).take 32 :=
  placementLeaf32.trans (NumericQueryFrameChecks.window_binding placementSource 32 32 (by decide +kernel))

numeric_data_binding placementLeaf64 : (data.placement.toList.drop 64).take 32 =
  NumericQueryFrameChecks.window placementSource 64 32 (by decide +kernel)

theorem placementSlice64 : (data.placement.toList.drop 64).take 32 = ((List.ofFn placementSource).drop 64).take 32 :=
  placementLeaf64.trans (NumericQueryFrameChecks.window_binding placementSource 64 32 (by decide +kernel))

numeric_data_binding placementLeaf96 : (data.placement.toList.drop 96).take 7 =
  NumericQueryFrameChecks.window placementSource 96 7 (by decide +kernel)

theorem placementSlice96 : (data.placement.toList.drop 96).take 7 = ((List.ofFn placementSource).drop 96).take 7 :=
  placementLeaf96.trans (NumericQueryFrameChecks.window_binding placementSource 96 7 (by decide +kernel))

theorem placementNode0_64 : (data.placement.toList.drop 0).take 64 = ((List.ofFn placementSource).drop 0).take 64 :=
  NumericQueryFrameChecks.merge_bindings data.placement.toList (List.ofFn placementSource) 0 32 32 placementSlice0 placementSlice32

theorem placementNode64_39 : (data.placement.toList.drop 64).take 39 = ((List.ofFn placementSource).drop 64).take 39 :=
  NumericQueryFrameChecks.merge_bindings data.placement.toList (List.ofFn placementSource) 64 32 7 placementSlice64 placementSlice96

theorem placementNode0_103 : (data.placement.toList.drop 0).take 103 = ((List.ofFn placementSource).drop 0).take 103 :=
  NumericQueryFrameChecks.merge_bindings data.placement.toList (List.ofFn placementSource) 0 64 39 placementNode0_64 placementNode64_39

theorem placement_fast_binding : data.placement.toList = (List.ofFn placementSource) :=
  NumericQueryFrameChecks.complete_binding data.placement.toList (List.ofFn placementSource) 103
    (by decide +kernel) List.length_ofFn placementNode0_103

end Airbender.Compiler.MemoryFrameChecks.ShiftBinopUncached
