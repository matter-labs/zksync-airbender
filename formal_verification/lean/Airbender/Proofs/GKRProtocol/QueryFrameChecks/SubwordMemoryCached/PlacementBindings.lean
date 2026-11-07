import Airbender.Proofs.GKRProtocol.QueryFrameChecks.SubwordMemoryCached.Data
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.QueryFrameChecks.SubwordMemoryCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def placementSource : Fin 66 → Nat := (fun wire : Fin 66 => (Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.inputBank.placement (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address wire)).val)

numeric_data_binding placementLeaf0 : (data.placement.drop 0).take 32 =
  NumericQueryFrameChecks.window placementSource 0 32 (by decide +kernel)

theorem placementSlice0 : (data.placement.drop 0).take 32 = ((List.ofFn placementSource).drop 0).take 32 :=
  placementLeaf0.trans (NumericQueryFrameChecks.window_binding placementSource 0 32 (by decide +kernel))

numeric_data_binding placementLeaf32 : (data.placement.drop 32).take 32 =
  NumericQueryFrameChecks.window placementSource 32 32 (by decide +kernel)

theorem placementSlice32 : (data.placement.drop 32).take 32 = ((List.ofFn placementSource).drop 32).take 32 :=
  placementLeaf32.trans (NumericQueryFrameChecks.window_binding placementSource 32 32 (by decide +kernel))

numeric_data_binding placementLeaf64 : (data.placement.drop 64).take 2 =
  NumericQueryFrameChecks.window placementSource 64 2 (by decide +kernel)

theorem placementSlice64 : (data.placement.drop 64).take 2 = ((List.ofFn placementSource).drop 64).take 2 :=
  placementLeaf64.trans (NumericQueryFrameChecks.window_binding placementSource 64 2 (by decide +kernel))

theorem placementNode32_34 : (data.placement.drop 32).take 34 = ((List.ofFn placementSource).drop 32).take 34 :=
  NumericQueryFrameChecks.merge_bindings data.placement (List.ofFn placementSource) 32 32 2 placementSlice32 placementSlice64

theorem placementNode0_66 : (data.placement.drop 0).take 66 = ((List.ofFn placementSource).drop 0).take 66 :=
  NumericQueryFrameChecks.merge_bindings data.placement (List.ofFn placementSource) 0 32 34 placementSlice0 placementNode32_34

theorem placement_binding : data.placement = (List.ofFn placementSource) :=
  NumericQueryFrameChecks.complete_binding data.placement (List.ofFn placementSource) 66
    (by decide +kernel) (List.length_ofFn) placementNode0_66

end Airbender.Compiler.QueryFrameChecks.SubwordMemoryCached
