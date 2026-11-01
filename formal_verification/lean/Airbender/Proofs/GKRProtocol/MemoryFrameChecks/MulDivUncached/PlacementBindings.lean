import Airbender.Proofs.GKRProtocol.MemoryFrameChecks.MulDivUncached.Data
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.MemoryFrameChecks.MulDivUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def placementSource : Fin 76 → Nat := (fun wire : Fin 76 => if wire.val < 71 then wire.val else (Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.inputBank.placement (Airbender.Compiler.MemoryNative.MulDivUncached.native.bank.address wire)).val)

numeric_data_binding placementLeaf0 : (data.placement.toList.drop 0).take 32 =
  NumericQueryFrameChecks.window placementSource 0 32 (by decide +kernel)

theorem placementSlice0 : (data.placement.toList.drop 0).take 32 = ((List.ofFn placementSource).drop 0).take 32 :=
  placementLeaf0.trans (NumericQueryFrameChecks.window_binding placementSource 0 32 (by decide +kernel))

numeric_data_binding placementLeaf32 : (data.placement.toList.drop 32).take 32 =
  NumericQueryFrameChecks.window placementSource 32 32 (by decide +kernel)

theorem placementSlice32 : (data.placement.toList.drop 32).take 32 = ((List.ofFn placementSource).drop 32).take 32 :=
  placementLeaf32.trans (NumericQueryFrameChecks.window_binding placementSource 32 32 (by decide +kernel))

numeric_data_binding placementLeaf64 : (data.placement.toList.drop 64).take 12 =
  NumericQueryFrameChecks.window placementSource 64 12 (by decide +kernel)

theorem placementSlice64 : (data.placement.toList.drop 64).take 12 = ((List.ofFn placementSource).drop 64).take 12 :=
  placementLeaf64.trans (NumericQueryFrameChecks.window_binding placementSource 64 12 (by decide +kernel))

theorem placementNode32_44 : (data.placement.toList.drop 32).take 44 = ((List.ofFn placementSource).drop 32).take 44 :=
  NumericQueryFrameChecks.merge_bindings data.placement.toList (List.ofFn placementSource) 32 32 12 placementSlice32 placementSlice64

theorem placementNode0_76 : (data.placement.toList.drop 0).take 76 = ((List.ofFn placementSource).drop 0).take 76 :=
  NumericQueryFrameChecks.merge_bindings data.placement.toList (List.ofFn placementSource) 0 32 44 placementSlice0 placementNode32_44

theorem placement_fast_binding : data.placement.toList = (List.ofFn placementSource) :=
  NumericQueryFrameChecks.complete_binding data.placement.toList (List.ofFn placementSource) 76
    (by decide +kernel) List.length_ofFn placementNode0_76

end Airbender.Compiler.MemoryFrameChecks.MulDivUncached
