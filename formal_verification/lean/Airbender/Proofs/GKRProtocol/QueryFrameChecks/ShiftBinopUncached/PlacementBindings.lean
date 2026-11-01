import Airbender.Proofs.GKRProtocol.QueryFrameChecks.ShiftBinopUncached.Data
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.QueryFrameChecks.ShiftBinopUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def placementSource : Fin 95 → Nat := (fun wire : Fin 95 => (Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.inputBank.placement (Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank.address wire)).val)

numeric_data_binding placementLeaf0 : (data.placement.drop 0).take 32 =
  NumericQueryFrameChecks.window placementSource 0 32 (by decide +kernel)

theorem placementSlice0 : (data.placement.drop 0).take 32 = ((List.ofFn placementSource).drop 0).take 32 :=
  placementLeaf0.trans (NumericQueryFrameChecks.window_binding placementSource 0 32 (by decide +kernel))

numeric_data_binding placementLeaf32 : (data.placement.drop 32).take 32 =
  NumericQueryFrameChecks.window placementSource 32 32 (by decide +kernel)

theorem placementSlice32 : (data.placement.drop 32).take 32 = ((List.ofFn placementSource).drop 32).take 32 :=
  placementLeaf32.trans (NumericQueryFrameChecks.window_binding placementSource 32 32 (by decide +kernel))

numeric_data_binding placementLeaf64 : (data.placement.drop 64).take 31 =
  NumericQueryFrameChecks.window placementSource 64 31 (by decide +kernel)

theorem placementSlice64 : (data.placement.drop 64).take 31 = ((List.ofFn placementSource).drop 64).take 31 :=
  placementLeaf64.trans (NumericQueryFrameChecks.window_binding placementSource 64 31 (by decide +kernel))

theorem placementNode32_63 : (data.placement.drop 32).take 63 = ((List.ofFn placementSource).drop 32).take 63 :=
  NumericQueryFrameChecks.merge_bindings data.placement (List.ofFn placementSource) 32 32 31 placementSlice32 placementSlice64

theorem placementNode0_95 : (data.placement.drop 0).take 95 = ((List.ofFn placementSource).drop 0).take 95 :=
  NumericQueryFrameChecks.merge_bindings data.placement (List.ofFn placementSource) 0 32 63 placementSlice0 placementNode32_63

theorem placement_binding : data.placement = (List.ofFn placementSource) :=
  NumericQueryFrameChecks.complete_binding data.placement (List.ofFn placementSource) 95
    (by decide +kernel) (List.length_ofFn) placementNode0_95

end Airbender.Compiler.QueryFrameChecks.ShiftBinopUncached
