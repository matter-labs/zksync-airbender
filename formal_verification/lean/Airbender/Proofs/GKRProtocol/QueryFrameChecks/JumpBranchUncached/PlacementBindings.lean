import Airbender.Proofs.GKRProtocol.QueryFrameChecks.JumpBranchUncached.Data
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.QueryFrameChecks.JumpBranchUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def placementSource : Fin 52 → Nat := (fun wire : Fin 52 => (Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.inputBank.placement (Airbender.Compiler.LookupSourceNative.JumpBranchUncached.native.bank.address wire)).val)

numeric_data_binding placementLeaf0 : (data.placement.drop 0).take 32 =
  NumericQueryFrameChecks.window placementSource 0 32 (by decide +kernel)

theorem placementSlice0 : (data.placement.drop 0).take 32 = ((List.ofFn placementSource).drop 0).take 32 :=
  placementLeaf0.trans (NumericQueryFrameChecks.window_binding placementSource 0 32 (by decide +kernel))

numeric_data_binding placementLeaf32 : (data.placement.drop 32).take 20 =
  NumericQueryFrameChecks.window placementSource 32 20 (by decide +kernel)

theorem placementSlice32 : (data.placement.drop 32).take 20 = ((List.ofFn placementSource).drop 32).take 20 :=
  placementLeaf32.trans (NumericQueryFrameChecks.window_binding placementSource 32 20 (by decide +kernel))

theorem placementNode0_52 : (data.placement.drop 0).take 52 = ((List.ofFn placementSource).drop 0).take 52 :=
  NumericQueryFrameChecks.merge_bindings data.placement (List.ofFn placementSource) 0 32 20 placementSlice0 placementSlice32

theorem placement_binding : data.placement = (List.ofFn placementSource) :=
  NumericQueryFrameChecks.complete_binding data.placement (List.ofFn placementSource) 52
    (by decide +kernel) (List.length_ofFn) placementNode0_52

end Airbender.Compiler.QueryFrameChecks.JumpBranchUncached
