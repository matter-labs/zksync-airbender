import Airbender.Proofs.GKRProtocol.MemoryFrameChecks.SubwordMemoryCached.Data
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.MemoryFrameChecks.SubwordMemoryCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def placementSource : Fin 74 → Nat := (fun wire : Fin 74 => if wire.val < 68 then wire.val else (Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.inputBank.placement (Airbender.Compiler.MemoryNative.SubwordMemoryCached.native.bank.address wire)).val)

numeric_data_binding placementLeaf0 : (data.placement.toList.drop 0).take 32 =
  NumericQueryFrameChecks.window placementSource 0 32 (by decide +kernel)

theorem placementSlice0 : (data.placement.toList.drop 0).take 32 = ((List.ofFn placementSource).drop 0).take 32 :=
  placementLeaf0.trans (NumericQueryFrameChecks.window_binding placementSource 0 32 (by decide +kernel))

numeric_data_binding placementLeaf32 : (data.placement.toList.drop 32).take 32 =
  NumericQueryFrameChecks.window placementSource 32 32 (by decide +kernel)

theorem placementSlice32 : (data.placement.toList.drop 32).take 32 = ((List.ofFn placementSource).drop 32).take 32 :=
  placementLeaf32.trans (NumericQueryFrameChecks.window_binding placementSource 32 32 (by decide +kernel))

numeric_data_binding placementLeaf64 : (data.placement.toList.drop 64).take 10 =
  NumericQueryFrameChecks.window placementSource 64 10 (by decide +kernel)

theorem placementSlice64 : (data.placement.toList.drop 64).take 10 = ((List.ofFn placementSource).drop 64).take 10 :=
  placementLeaf64.trans (NumericQueryFrameChecks.window_binding placementSource 64 10 (by decide +kernel))

theorem placementNode32_42 : (data.placement.toList.drop 32).take 42 = ((List.ofFn placementSource).drop 32).take 42 :=
  NumericQueryFrameChecks.merge_bindings data.placement.toList (List.ofFn placementSource) 32 32 10 placementSlice32 placementSlice64

theorem placementNode0_74 : (data.placement.toList.drop 0).take 74 = ((List.ofFn placementSource).drop 0).take 74 :=
  NumericQueryFrameChecks.merge_bindings data.placement.toList (List.ofFn placementSource) 0 32 42 placementSlice0 placementNode32_42

theorem placement_fast_binding : data.placement.toList = (List.ofFn placementSource) :=
  NumericQueryFrameChecks.complete_binding data.placement.toList (List.ofFn placementSource) 74
    (by decide +kernel) List.length_ofFn placementNode0_74

end Airbender.Compiler.MemoryFrameChecks.SubwordMemoryCached
