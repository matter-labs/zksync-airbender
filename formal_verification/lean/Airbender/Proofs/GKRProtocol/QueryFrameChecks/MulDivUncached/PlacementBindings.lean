import Airbender.Proofs.GKRProtocol.QueryFrameChecks.MulDivUncached.Data
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.QueryFrameChecks.MulDivUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def placementSource : Fin 68 → Nat := (fun wire : Fin 68 => (Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.inputBank.placement (Airbender.Compiler.LookupSourceNative.MulDivUncached.native.bank.address wire)).val)

numeric_data_binding placementLeaf0 : (data.placement.drop 0).take 32 =
  NumericQueryFrameChecks.window placementSource 0 32 (by decide +kernel)

theorem placementSlice0 : (data.placement.drop 0).take 32 = ((List.ofFn placementSource).drop 0).take 32 :=
  placementLeaf0.trans (NumericQueryFrameChecks.window_binding placementSource 0 32 (by decide +kernel))

numeric_data_binding placementLeaf32 : (data.placement.drop 32).take 32 =
  NumericQueryFrameChecks.window placementSource 32 32 (by decide +kernel)

theorem placementSlice32 : (data.placement.drop 32).take 32 = ((List.ofFn placementSource).drop 32).take 32 :=
  placementLeaf32.trans (NumericQueryFrameChecks.window_binding placementSource 32 32 (by decide +kernel))

numeric_data_binding placementLeaf64 : (data.placement.drop 64).take 4 =
  NumericQueryFrameChecks.window placementSource 64 4 (by decide +kernel)

theorem placementSlice64 : (data.placement.drop 64).take 4 = ((List.ofFn placementSource).drop 64).take 4 :=
  placementLeaf64.trans (NumericQueryFrameChecks.window_binding placementSource 64 4 (by decide +kernel))

theorem placementNode32_36 : (data.placement.drop 32).take 36 = ((List.ofFn placementSource).drop 32).take 36 :=
  NumericQueryFrameChecks.merge_bindings data.placement (List.ofFn placementSource) 32 32 4 placementSlice32 placementSlice64

theorem placementNode0_68 : (data.placement.drop 0).take 68 = ((List.ofFn placementSource).drop 0).take 68 :=
  NumericQueryFrameChecks.merge_bindings data.placement (List.ofFn placementSource) 0 32 36 placementSlice0 placementNode32_36

theorem placement_binding : data.placement = (List.ofFn placementSource) :=
  NumericQueryFrameChecks.complete_binding data.placement (List.ofFn placementSource) 68
    (by decide +kernel) (List.length_ofFn) placementNode0_68

end Airbender.Compiler.QueryFrameChecks.MulDivUncached
