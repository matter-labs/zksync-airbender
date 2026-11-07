import Airbender.Proofs.GKRProtocol.QueryFrameChecks.JumpBranchCached.Data
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.QueryFrameChecks.JumpBranchCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def placementSource : Fin 54 → Nat := (fun wire : Fin 54 => (Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.inputBank.placement (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.bank.address wire)).val)

numeric_data_binding placementLeaf0 : (data.placement.drop 0).take 32 =
  NumericQueryFrameChecks.window placementSource 0 32 (by decide +kernel)

theorem placementSlice0 : (data.placement.drop 0).take 32 = ((List.ofFn placementSource).drop 0).take 32 :=
  placementLeaf0.trans (NumericQueryFrameChecks.window_binding placementSource 0 32 (by decide +kernel))

numeric_data_binding placementLeaf32 : (data.placement.drop 32).take 22 =
  NumericQueryFrameChecks.window placementSource 32 22 (by decide +kernel)

theorem placementSlice32 : (data.placement.drop 32).take 22 = ((List.ofFn placementSource).drop 32).take 22 :=
  placementLeaf32.trans (NumericQueryFrameChecks.window_binding placementSource 32 22 (by decide +kernel))

theorem placementNode0_54 : (data.placement.drop 0).take 54 = ((List.ofFn placementSource).drop 0).take 54 :=
  NumericQueryFrameChecks.merge_bindings data.placement (List.ofFn placementSource) 0 32 22 placementSlice0 placementSlice32

theorem placement_binding : data.placement = (List.ofFn placementSource) :=
  NumericQueryFrameChecks.complete_binding data.placement (List.ofFn placementSource) 54
    (by decide +kernel) (List.length_ofFn) placementNode0_54

end Airbender.Compiler.QueryFrameChecks.JumpBranchCached
