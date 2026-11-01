import Airbender.Proofs.GKRProtocol.MemoryFrameChecks.SubwordMemoryUncached.Data
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.MemoryFrameChecks.SubwordMemoryUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def placementSource : Fin 72 → Nat := (fun wire : Fin 72 => if wire.val < 68 then wire.val else (Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.inputBank.placement (Airbender.Compiler.MemoryNative.SubwordMemoryUncached.native.bank.address wire)).val)

numeric_data_binding placementLeaf0 : (data.placement.toList.drop 0).take 32 =
  NumericQueryFrameChecks.window placementSource 0 32 (by decide +kernel)

theorem placementSlice0 : (data.placement.toList.drop 0).take 32 = ((List.ofFn placementSource).drop 0).take 32 :=
  placementLeaf0.trans (NumericQueryFrameChecks.window_binding placementSource 0 32 (by decide +kernel))

numeric_data_binding placementLeaf32 : (data.placement.toList.drop 32).take 32 =
  NumericQueryFrameChecks.window placementSource 32 32 (by decide +kernel)

theorem placementSlice32 : (data.placement.toList.drop 32).take 32 = ((List.ofFn placementSource).drop 32).take 32 :=
  placementLeaf32.trans (NumericQueryFrameChecks.window_binding placementSource 32 32 (by decide +kernel))

numeric_data_binding placementLeaf64 : (data.placement.toList.drop 64).take 8 =
  NumericQueryFrameChecks.window placementSource 64 8 (by decide +kernel)

theorem placementSlice64 : (data.placement.toList.drop 64).take 8 = ((List.ofFn placementSource).drop 64).take 8 :=
  placementLeaf64.trans (NumericQueryFrameChecks.window_binding placementSource 64 8 (by decide +kernel))

theorem placementNode32_40 : (data.placement.toList.drop 32).take 40 = ((List.ofFn placementSource).drop 32).take 40 :=
  NumericQueryFrameChecks.merge_bindings data.placement.toList (List.ofFn placementSource) 32 32 8 placementSlice32 placementSlice64

theorem placementNode0_72 : (data.placement.toList.drop 0).take 72 = ((List.ofFn placementSource).drop 0).take 72 :=
  NumericQueryFrameChecks.merge_bindings data.placement.toList (List.ofFn placementSource) 0 32 40 placementSlice0 placementNode32_40

theorem placement_fast_binding : data.placement.toList = (List.ofFn placementSource) :=
  NumericQueryFrameChecks.complete_binding data.placement.toList (List.ofFn placementSource) 72
    (by decide +kernel) List.length_ofFn placementNode0_72

end Airbender.Compiler.MemoryFrameChecks.SubwordMemoryUncached
