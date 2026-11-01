import Airbender.Proofs.GKRProtocol.QueryFrameChecks.KeccakUncached.Data
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.QueryFrameChecks.KeccakUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def placementSource : Fin 226 → Nat := (fun wire : Fin 226 => (Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.inputBank.placement (Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank.address wire)).val)

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

numeric_data_binding placementLeaf192 : (data.placement.drop 192).take 32 =
  NumericQueryFrameChecks.window placementSource 192 32 (by decide +kernel)

theorem placementSlice192 : (data.placement.drop 192).take 32 = ((List.ofFn placementSource).drop 192).take 32 :=
  placementLeaf192.trans (NumericQueryFrameChecks.window_binding placementSource 192 32 (by decide +kernel))

numeric_data_binding placementLeaf224 : (data.placement.drop 224).take 2 =
  NumericQueryFrameChecks.window placementSource 224 2 (by decide +kernel)

theorem placementSlice224 : (data.placement.drop 224).take 2 = ((List.ofFn placementSource).drop 224).take 2 :=
  placementLeaf224.trans (NumericQueryFrameChecks.window_binding placementSource 224 2 (by decide +kernel))

theorem placementNode0_64 : (data.placement.drop 0).take 64 = ((List.ofFn placementSource).drop 0).take 64 :=
  NumericQueryFrameChecks.merge_bindings data.placement (List.ofFn placementSource) 0 32 32 placementSlice0 placementSlice32

theorem placementNode64_64 : (data.placement.drop 64).take 64 = ((List.ofFn placementSource).drop 64).take 64 :=
  NumericQueryFrameChecks.merge_bindings data.placement (List.ofFn placementSource) 64 32 32 placementSlice64 placementSlice96

theorem placementNode0_128 : (data.placement.drop 0).take 128 = ((List.ofFn placementSource).drop 0).take 128 :=
  NumericQueryFrameChecks.merge_bindings data.placement (List.ofFn placementSource) 0 64 64 placementNode0_64 placementNode64_64

theorem placementNode128_64 : (data.placement.drop 128).take 64 = ((List.ofFn placementSource).drop 128).take 64 :=
  NumericQueryFrameChecks.merge_bindings data.placement (List.ofFn placementSource) 128 32 32 placementSlice128 placementSlice160

theorem placementNode192_34 : (data.placement.drop 192).take 34 = ((List.ofFn placementSource).drop 192).take 34 :=
  NumericQueryFrameChecks.merge_bindings data.placement (List.ofFn placementSource) 192 32 2 placementSlice192 placementSlice224

theorem placementNode128_98 : (data.placement.drop 128).take 98 = ((List.ofFn placementSource).drop 128).take 98 :=
  NumericQueryFrameChecks.merge_bindings data.placement (List.ofFn placementSource) 128 64 34 placementNode128_64 placementNode192_34

theorem placementNode0_226 : (data.placement.drop 0).take 226 = ((List.ofFn placementSource).drop 0).take 226 :=
  NumericQueryFrameChecks.merge_bindings data.placement (List.ofFn placementSource) 0 128 98 placementNode0_128 placementNode128_98

theorem placement_binding : data.placement = (List.ofFn placementSource) :=
  NumericQueryFrameChecks.complete_binding data.placement (List.ofFn placementSource) 226
    (by decide +kernel) (List.length_ofFn) placementNode0_226

end Airbender.Compiler.QueryFrameChecks.KeccakUncached
