import Airbender.Proofs.GKRProtocol.QueryFrameChecks.BlakeGUncached.Data
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.QueryFrameChecks.BlakeGUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def placementSource : Fin 87 → Nat := (fun wire : Fin 87 => (Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.inputBank.placement (Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.address wire)).val)

numeric_data_binding placementLeaf0 : (data.placement.drop 0).take 32 =
  NumericQueryFrameChecks.window placementSource 0 32 (by decide +kernel)

theorem placementSlice0 : (data.placement.drop 0).take 32 = ((List.ofFn placementSource).drop 0).take 32 :=
  placementLeaf0.trans (NumericQueryFrameChecks.window_binding placementSource 0 32 (by decide +kernel))

numeric_data_binding placementLeaf32 : (data.placement.drop 32).take 32 =
  NumericQueryFrameChecks.window placementSource 32 32 (by decide +kernel)

theorem placementSlice32 : (data.placement.drop 32).take 32 = ((List.ofFn placementSource).drop 32).take 32 :=
  placementLeaf32.trans (NumericQueryFrameChecks.window_binding placementSource 32 32 (by decide +kernel))

numeric_data_binding placementLeaf64 : (data.placement.drop 64).take 23 =
  NumericQueryFrameChecks.window placementSource 64 23 (by decide +kernel)

theorem placementSlice64 : (data.placement.drop 64).take 23 = ((List.ofFn placementSource).drop 64).take 23 :=
  placementLeaf64.trans (NumericQueryFrameChecks.window_binding placementSource 64 23 (by decide +kernel))

theorem placementNode32_55 : (data.placement.drop 32).take 55 = ((List.ofFn placementSource).drop 32).take 55 :=
  NumericQueryFrameChecks.merge_bindings data.placement (List.ofFn placementSource) 32 32 23 placementSlice32 placementSlice64

theorem placementNode0_87 : (data.placement.drop 0).take 87 = ((List.ofFn placementSource).drop 0).take 87 :=
  NumericQueryFrameChecks.merge_bindings data.placement (List.ofFn placementSource) 0 32 55 placementSlice0 placementNode32_55

theorem placement_binding : data.placement = (List.ofFn placementSource) :=
  NumericQueryFrameChecks.complete_binding data.placement (List.ofFn placementSource) 87
    (by decide +kernel) (List.length_ofFn) placementNode0_87

end Airbender.Compiler.QueryFrameChecks.BlakeGUncached
