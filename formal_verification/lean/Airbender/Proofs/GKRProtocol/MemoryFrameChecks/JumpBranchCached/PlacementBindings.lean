import Airbender.Proofs.GKRProtocol.MemoryFrameChecks.JumpBranchCached.Data
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.MemoryFrameChecks.JumpBranchCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def placementSource : Fin 62 → Nat := (fun wire : Fin 62 => if wire.val < 55 then wire.val else (Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.inputBank.placement (Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank.address wire)).val)

numeric_data_binding placementLeaf0 : (data.placement.toList.drop 0).take 32 =
  NumericQueryFrameChecks.window placementSource 0 32 (by decide +kernel)

theorem placementSlice0 : (data.placement.toList.drop 0).take 32 = ((List.ofFn placementSource).drop 0).take 32 :=
  placementLeaf0.trans (NumericQueryFrameChecks.window_binding placementSource 0 32 (by decide +kernel))

numeric_data_binding placementLeaf32 : (data.placement.toList.drop 32).take 30 =
  NumericQueryFrameChecks.window placementSource 32 30 (by decide +kernel)

theorem placementSlice32 : (data.placement.toList.drop 32).take 30 = ((List.ofFn placementSource).drop 32).take 30 :=
  placementLeaf32.trans (NumericQueryFrameChecks.window_binding placementSource 32 30 (by decide +kernel))

theorem placementNode0_62 : (data.placement.toList.drop 0).take 62 = ((List.ofFn placementSource).drop 0).take 62 :=
  NumericQueryFrameChecks.merge_bindings data.placement.toList (List.ofFn placementSource) 0 32 30 placementSlice0 placementSlice32

theorem placement_fast_binding : data.placement.toList = (List.ofFn placementSource) :=
  NumericQueryFrameChecks.complete_binding data.placement.toList (List.ofFn placementSource) 62
    (by decide +kernel) List.length_ofFn placementNode0_62

end Airbender.Compiler.MemoryFrameChecks.JumpBranchCached
