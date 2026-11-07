import Airbender.Proofs.GKRProtocol.QueryFrameChecks.MulDivCached.Data
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.QueryFrameChecks.MulDivCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def placementSource : Fin 70 → Nat := (fun wire : Fin 70 => (Airbender.Compiler.FullArithmeticNative.MulDivCached.native.inputBank.placement (Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address wire)).val)

numeric_data_binding placementLeaf0 : (data.placement.drop 0).take 32 =
  NumericQueryFrameChecks.window placementSource 0 32 (by decide +kernel)

theorem placementSlice0 : (data.placement.drop 0).take 32 = ((List.ofFn placementSource).drop 0).take 32 :=
  placementLeaf0.trans (NumericQueryFrameChecks.window_binding placementSource 0 32 (by decide +kernel))

numeric_data_binding placementLeaf32 : (data.placement.drop 32).take 32 =
  NumericQueryFrameChecks.window placementSource 32 32 (by decide +kernel)

theorem placementSlice32 : (data.placement.drop 32).take 32 = ((List.ofFn placementSource).drop 32).take 32 :=
  placementLeaf32.trans (NumericQueryFrameChecks.window_binding placementSource 32 32 (by decide +kernel))

numeric_data_binding placementLeaf64 : (data.placement.drop 64).take 6 =
  NumericQueryFrameChecks.window placementSource 64 6 (by decide +kernel)

theorem placementSlice64 : (data.placement.drop 64).take 6 = ((List.ofFn placementSource).drop 64).take 6 :=
  placementLeaf64.trans (NumericQueryFrameChecks.window_binding placementSource 64 6 (by decide +kernel))

theorem placementNode32_38 : (data.placement.drop 32).take 38 = ((List.ofFn placementSource).drop 32).take 38 :=
  NumericQueryFrameChecks.merge_bindings data.placement (List.ofFn placementSource) 32 32 6 placementSlice32 placementSlice64

theorem placementNode0_70 : (data.placement.drop 0).take 70 = ((List.ofFn placementSource).drop 0).take 70 :=
  NumericQueryFrameChecks.merge_bindings data.placement (List.ofFn placementSource) 0 32 38 placementSlice0 placementNode32_38

theorem placement_binding : data.placement = (List.ofFn placementSource) :=
  NumericQueryFrameChecks.complete_binding data.placement (List.ofFn placementSource) 70
    (by decide +kernel) (List.length_ofFn) placementNode0_70

end Airbender.Compiler.QueryFrameChecks.MulDivCached
