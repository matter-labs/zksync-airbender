import Airbender.Proofs.GKRProtocol.MemoryFrameChecks.BlakeGCached.Data
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.MemoryFrameChecks.BlakeGCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def placementSource : Fin 118 → Nat := (fun wire : Fin 118 => if wire.val < 112 then wire.val else (Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.inputBank.placement (Airbender.Compiler.MemoryNative.BlakeGCached.native.bank.address wire)).val)

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

numeric_data_binding placementLeaf96 : (data.placement.toList.drop 96).take 22 =
  NumericQueryFrameChecks.window placementSource 96 22 (by decide +kernel)

theorem placementSlice96 : (data.placement.toList.drop 96).take 22 = ((List.ofFn placementSource).drop 96).take 22 :=
  placementLeaf96.trans (NumericQueryFrameChecks.window_binding placementSource 96 22 (by decide +kernel))

theorem placementNode0_64 : (data.placement.toList.drop 0).take 64 = ((List.ofFn placementSource).drop 0).take 64 :=
  NumericQueryFrameChecks.merge_bindings data.placement.toList (List.ofFn placementSource) 0 32 32 placementSlice0 placementSlice32

theorem placementNode64_54 : (data.placement.toList.drop 64).take 54 = ((List.ofFn placementSource).drop 64).take 54 :=
  NumericQueryFrameChecks.merge_bindings data.placement.toList (List.ofFn placementSource) 64 32 22 placementSlice64 placementSlice96

theorem placementNode0_118 : (data.placement.toList.drop 0).take 118 = ((List.ofFn placementSource).drop 0).take 118 :=
  NumericQueryFrameChecks.merge_bindings data.placement.toList (List.ofFn placementSource) 0 64 54 placementNode0_64 placementNode64_54

theorem placement_fast_binding : data.placement.toList = (List.ofFn placementSource) :=
  NumericQueryFrameChecks.complete_binding data.placement.toList (List.ofFn placementSource) 118
    (by decide +kernel) List.length_ofFn placementNode0_118

end Airbender.Compiler.MemoryFrameChecks.BlakeGCached
