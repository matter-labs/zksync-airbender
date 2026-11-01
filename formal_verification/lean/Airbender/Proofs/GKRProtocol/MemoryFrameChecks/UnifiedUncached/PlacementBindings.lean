import Airbender.Proofs.GKRProtocol.MemoryFrameChecks.UnifiedUncached.Data
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.MemoryFrameChecks.UnifiedUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def placementSource : Fin 142 → Nat := (fun wire : Fin 142 => if wire.val < 137 then wire.val else (Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.inputBank.placement (Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank.address wire)).val)

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

numeric_data_binding placementLeaf96 : (data.placement.toList.drop 96).take 32 =
  NumericQueryFrameChecks.window placementSource 96 32 (by decide +kernel)

theorem placementSlice96 : (data.placement.toList.drop 96).take 32 = ((List.ofFn placementSource).drop 96).take 32 :=
  placementLeaf96.trans (NumericQueryFrameChecks.window_binding placementSource 96 32 (by decide +kernel))

numeric_data_binding placementLeaf128 : (data.placement.toList.drop 128).take 14 =
  NumericQueryFrameChecks.window placementSource 128 14 (by decide +kernel)

theorem placementSlice128 : (data.placement.toList.drop 128).take 14 = ((List.ofFn placementSource).drop 128).take 14 :=
  placementLeaf128.trans (NumericQueryFrameChecks.window_binding placementSource 128 14 (by decide +kernel))

theorem placementNode0_64 : (data.placement.toList.drop 0).take 64 = ((List.ofFn placementSource).drop 0).take 64 :=
  NumericQueryFrameChecks.merge_bindings data.placement.toList (List.ofFn placementSource) 0 32 32 placementSlice0 placementSlice32

theorem placementNode96_46 : (data.placement.toList.drop 96).take 46 = ((List.ofFn placementSource).drop 96).take 46 :=
  NumericQueryFrameChecks.merge_bindings data.placement.toList (List.ofFn placementSource) 96 32 14 placementSlice96 placementSlice128

theorem placementNode64_78 : (data.placement.toList.drop 64).take 78 = ((List.ofFn placementSource).drop 64).take 78 :=
  NumericQueryFrameChecks.merge_bindings data.placement.toList (List.ofFn placementSource) 64 32 46 placementSlice64 placementNode96_46

theorem placementNode0_142 : (data.placement.toList.drop 0).take 142 = ((List.ofFn placementSource).drop 0).take 142 :=
  NumericQueryFrameChecks.merge_bindings data.placement.toList (List.ofFn placementSource) 0 64 78 placementNode0_64 placementNode64_78

theorem placement_fast_binding : data.placement.toList = (List.ofFn placementSource) :=
  NumericQueryFrameChecks.complete_binding data.placement.toList (List.ofFn placementSource) 142
    (by decide +kernel) List.length_ofFn placementNode0_142

end Airbender.Compiler.MemoryFrameChecks.UnifiedUncached
