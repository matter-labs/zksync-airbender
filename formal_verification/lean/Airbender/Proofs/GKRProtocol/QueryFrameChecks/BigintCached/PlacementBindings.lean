import Airbender.Proofs.GKRProtocol.QueryFrameChecks.BigintCached.Data
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.QueryFrameChecks.BigintCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def placementSource : Fin 222 → Nat := (fun wire : Fin 222 => (Airbender.Compiler.FullArithmeticNative.BigintCached.native.inputBank.placement (Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.address wire)).val)

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

numeric_data_binding placementLeaf96 : (data.placement.drop 96).take 32 =
  NumericQueryFrameChecks.window placementSource 96 32 (by decide +kernel)

theorem placementSlice96 : (data.placement.drop 96).take 32 = ((List.ofFn placementSource).drop 96).take 32 :=
  placementLeaf96.trans (NumericQueryFrameChecks.window_binding placementSource 96 32 (by decide +kernel))

numeric_data_binding placementLeaf128 : (data.placement.drop 128).take 32 =
  NumericQueryFrameChecks.window placementSource 128 32 (by decide +kernel)

theorem placementSlice128 : (data.placement.drop 128).take 32 = ((List.ofFn placementSource).drop 128).take 32 :=
  placementLeaf128.trans (NumericQueryFrameChecks.window_binding placementSource 128 32 (by decide +kernel))

numeric_data_binding placementLeaf160 : (data.placement.drop 160).take 32 =
  NumericQueryFrameChecks.window placementSource 160 32 (by decide +kernel)

theorem placementSlice160 : (data.placement.drop 160).take 32 = ((List.ofFn placementSource).drop 160).take 32 :=
  placementLeaf160.trans (NumericQueryFrameChecks.window_binding placementSource 160 32 (by decide +kernel))

numeric_data_binding placementLeaf192 : (data.placement.drop 192).take 30 =
  NumericQueryFrameChecks.window placementSource 192 30 (by decide +kernel)

theorem placementSlice192 : (data.placement.drop 192).take 30 = ((List.ofFn placementSource).drop 192).take 30 :=
  placementLeaf192.trans (NumericQueryFrameChecks.window_binding placementSource 192 30 (by decide +kernel))

theorem placementNode32_64 : (data.placement.drop 32).take 64 = ((List.ofFn placementSource).drop 32).take 64 :=
  NumericQueryFrameChecks.merge_bindings data.placement (List.ofFn placementSource) 32 32 32 placementSlice32 placementSlice64

theorem placementNode0_96 : (data.placement.drop 0).take 96 = ((List.ofFn placementSource).drop 0).take 96 :=
  NumericQueryFrameChecks.merge_bindings data.placement (List.ofFn placementSource) 0 32 64 placementSlice0 placementNode32_64

theorem placementNode96_64 : (data.placement.drop 96).take 64 = ((List.ofFn placementSource).drop 96).take 64 :=
  NumericQueryFrameChecks.merge_bindings data.placement (List.ofFn placementSource) 96 32 32 placementSlice96 placementSlice128

theorem placementNode160_62 : (data.placement.drop 160).take 62 = ((List.ofFn placementSource).drop 160).take 62 :=
  NumericQueryFrameChecks.merge_bindings data.placement (List.ofFn placementSource) 160 32 30 placementSlice160 placementSlice192

theorem placementNode96_126 : (data.placement.drop 96).take 126 = ((List.ofFn placementSource).drop 96).take 126 :=
  NumericQueryFrameChecks.merge_bindings data.placement (List.ofFn placementSource) 96 64 62 placementNode96_64 placementNode160_62

theorem placementNode0_222 : (data.placement.drop 0).take 222 = ((List.ofFn placementSource).drop 0).take 222 :=
  NumericQueryFrameChecks.merge_bindings data.placement (List.ofFn placementSource) 0 96 126 placementNode0_96 placementNode96_126

theorem placement_binding : data.placement = (List.ofFn placementSource) :=
  NumericQueryFrameChecks.complete_binding data.placement (List.ofFn placementSource) 222
    (by decide +kernel) (List.length_ofFn) placementNode0_222

end Airbender.Compiler.QueryFrameChecks.BigintCached
