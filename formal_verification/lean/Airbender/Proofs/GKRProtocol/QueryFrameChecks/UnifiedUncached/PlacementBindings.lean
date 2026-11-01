import Airbender.Proofs.GKRProtocol.QueryFrameChecks.UnifiedUncached.Data
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.QueryFrameChecks.UnifiedUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def placementSource : Fin 126 → Nat := (fun wire : Fin 126 => (Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.inputBank.placement (Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.bank.address wire)).val)

numeric_data_binding placementLeaf0 : (data.placement.drop 0).take 32 =
  NumericQueryFrameChecks.window placementSource 0 32 (by decide +kernel)

theorem placementSlice0 : (data.placement.drop 0).take 32 = ((List.ofFn placementSource).drop 0).take 32 :=
  placementLeaf0.trans (NumericQueryFrameChecks.window_binding placementSource 0 32 (by decide +kernel))

numeric_data_binding placementLeaf32 : (data.placement.drop 32).take 32 =
  NumericQueryFrameChecks.window placementSource 32 32 (by decide +kernel)

theorem placementSlice32 : (data.placement.drop 32).take 32 = ((List.ofFn placementSource).drop 32).take 32 :=
  placementLeaf32.trans (NumericQueryFrameChecks.window_binding placementSource 32 32 (by decide +kernel))

numeric_data_binding placementLeaf64 : (data.placement.drop 64).take 32 =
  NumericQueryFrameChecks.window placementSource 64 32 (by decide +kernel)

theorem placementSlice64 : (data.placement.drop 64).take 32 = ((List.ofFn placementSource).drop 64).take 32 :=
  placementLeaf64.trans (NumericQueryFrameChecks.window_binding placementSource 64 32 (by decide +kernel))

numeric_data_binding placementLeaf96 : (data.placement.drop 96).take 30 =
  NumericQueryFrameChecks.window placementSource 96 30 (by decide +kernel)

theorem placementSlice96 : (data.placement.drop 96).take 30 = ((List.ofFn placementSource).drop 96).take 30 :=
  placementLeaf96.trans (NumericQueryFrameChecks.window_binding placementSource 96 30 (by decide +kernel))

theorem placementNode0_64 : (data.placement.drop 0).take 64 = ((List.ofFn placementSource).drop 0).take 64 :=
  NumericQueryFrameChecks.merge_bindings data.placement (List.ofFn placementSource) 0 32 32 placementSlice0 placementSlice32

theorem placementNode64_62 : (data.placement.drop 64).take 62 = ((List.ofFn placementSource).drop 64).take 62 :=
  NumericQueryFrameChecks.merge_bindings data.placement (List.ofFn placementSource) 64 32 30 placementSlice64 placementSlice96

theorem placementNode0_126 : (data.placement.drop 0).take 126 = ((List.ofFn placementSource).drop 0).take 126 :=
  NumericQueryFrameChecks.merge_bindings data.placement (List.ofFn placementSource) 0 64 62 placementNode0_64 placementNode64_62

theorem placement_binding : data.placement = (List.ofFn placementSource) :=
  NumericQueryFrameChecks.complete_binding data.placement (List.ofFn placementSource) 126
    (by decide +kernel) (List.length_ofFn) placementNode0_126

end Airbender.Compiler.QueryFrameChecks.UnifiedUncached
