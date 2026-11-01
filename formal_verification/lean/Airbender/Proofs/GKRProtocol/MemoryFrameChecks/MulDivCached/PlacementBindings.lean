import Airbender.Proofs.GKRProtocol.MemoryFrameChecks.MulDivCached.Data
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.MemoryFrameChecks.MulDivCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def placementSource : Fin 78 → Nat := (fun wire : Fin 78 => if wire.val < 71 then wire.val else (Airbender.Compiler.FullArithmeticNative.MulDivCached.native.inputBank.placement (Airbender.Compiler.MemoryNative.MulDivCached.native.bank.address wire)).val)

numeric_data_binding placementLeaf0 : (data.placement.toList.drop 0).take 32 =
  NumericQueryFrameChecks.window placementSource 0 32 (by decide +kernel)

theorem placementSlice0 : (data.placement.toList.drop 0).take 32 = ((List.ofFn placementSource).drop 0).take 32 :=
  placementLeaf0.trans (NumericQueryFrameChecks.window_binding placementSource 0 32 (by decide +kernel))

numeric_data_binding placementLeaf32 : (data.placement.toList.drop 32).take 32 =
  NumericQueryFrameChecks.window placementSource 32 32 (by decide +kernel)

theorem placementSlice32 : (data.placement.toList.drop 32).take 32 = ((List.ofFn placementSource).drop 32).take 32 :=
  placementLeaf32.trans (NumericQueryFrameChecks.window_binding placementSource 32 32 (by decide +kernel))

numeric_data_binding placementLeaf64 : (data.placement.toList.drop 64).take 14 =
  NumericQueryFrameChecks.window placementSource 64 14 (by decide +kernel)

theorem placementSlice64 : (data.placement.toList.drop 64).take 14 = ((List.ofFn placementSource).drop 64).take 14 :=
  placementLeaf64.trans (NumericQueryFrameChecks.window_binding placementSource 64 14 (by decide +kernel))

theorem placementNode32_46 : (data.placement.toList.drop 32).take 46 = ((List.ofFn placementSource).drop 32).take 46 :=
  NumericQueryFrameChecks.merge_bindings data.placement.toList (List.ofFn placementSource) 32 32 14 placementSlice32 placementSlice64

theorem placementNode0_78 : (data.placement.toList.drop 0).take 78 = ((List.ofFn placementSource).drop 0).take 78 :=
  NumericQueryFrameChecks.merge_bindings data.placement.toList (List.ofFn placementSource) 0 32 46 placementSlice0 placementNode32_46

theorem placement_fast_binding : data.placement.toList = (List.ofFn placementSource) :=
  NumericQueryFrameChecks.complete_binding data.placement.toList (List.ofFn placementSource) 78
    (by decide +kernel) List.length_ofFn placementNode0_78

end Airbender.Compiler.MemoryFrameChecks.MulDivCached
