import Airbender.Proofs.GKRProtocol.MemoryFrameChecks.BigintUncached.Data
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.MemoryFrameChecks.BigintUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def placementSource : Fin 284 → Nat := (fun wire : Fin 284 => if wire.val < 276 then wire.val else (Airbender.Compiler.FullArithmeticNative.BigintUncached.native.inputBank.placement (Airbender.Compiler.MemoryNative.BigintUncached.native.bank.address wire)).val)

numeric_data_binding placementLeaf0 : (data.placement.toList.drop 0).take 32 =
  NumericQueryFrameChecks.window placementSource 0 32 (by decide +kernel)

theorem placementSlice0 : (data.placement.toList.drop 0).take 32 = ((List.ofFn placementSource).drop 0).take 32 :=
  placementLeaf0.trans (NumericQueryFrameChecks.window_binding placementSource 0 32 (by decide +kernel))

numeric_data_binding placementLeaf32 : (data.placement.toList.drop 32).take 32 =
  NumericQueryFrameChecks.window placementSource 32 32 (by decide +kernel)

theorem placementSlice32 : (data.placement.toList.drop 32).take 32 = ((List.ofFn placementSource).drop 32).take 32 :=
  placementLeaf32.trans (NumericQueryFrameChecks.window_binding placementSource 32 32 (by decide +kernel))

numeric_data_binding placementLeaf64 : (data.placement.toList.drop 64).take 32 =
  NumericQueryFrameChecks.window placementSource 64 32 (by decide +kernel)

theorem placementSlice64 : (data.placement.toList.drop 64).take 32 = ((List.ofFn placementSource).drop 64).take 32 :=
  placementLeaf64.trans (NumericQueryFrameChecks.window_binding placementSource 64 32 (by decide +kernel))

numeric_data_binding placementLeaf96 : (data.placement.toList.drop 96).take 32 =
  NumericQueryFrameChecks.window placementSource 96 32 (by decide +kernel)

theorem placementSlice96 : (data.placement.toList.drop 96).take 32 = ((List.ofFn placementSource).drop 96).take 32 :=
  placementLeaf96.trans (NumericQueryFrameChecks.window_binding placementSource 96 32 (by decide +kernel))

numeric_data_binding placementLeaf128 : (data.placement.toList.drop 128).take 32 =
  NumericQueryFrameChecks.window placementSource 128 32 (by decide +kernel)

theorem placementSlice128 : (data.placement.toList.drop 128).take 32 = ((List.ofFn placementSource).drop 128).take 32 :=
  placementLeaf128.trans (NumericQueryFrameChecks.window_binding placementSource 128 32 (by decide +kernel))

numeric_data_binding placementLeaf160 : (data.placement.toList.drop 160).take 32 =
  NumericQueryFrameChecks.window placementSource 160 32 (by decide +kernel)

theorem placementSlice160 : (data.placement.toList.drop 160).take 32 = ((List.ofFn placementSource).drop 160).take 32 :=
  placementLeaf160.trans (NumericQueryFrameChecks.window_binding placementSource 160 32 (by decide +kernel))

numeric_data_binding placementLeaf192 : (data.placement.toList.drop 192).take 32 =
  NumericQueryFrameChecks.window placementSource 192 32 (by decide +kernel)

theorem placementSlice192 : (data.placement.toList.drop 192).take 32 = ((List.ofFn placementSource).drop 192).take 32 :=
  placementLeaf192.trans (NumericQueryFrameChecks.window_binding placementSource 192 32 (by decide +kernel))

numeric_data_binding placementLeaf224 : (data.placement.toList.drop 224).take 32 =
  NumericQueryFrameChecks.window placementSource 224 32 (by decide +kernel)

theorem placementSlice224 : (data.placement.toList.drop 224).take 32 = ((List.ofFn placementSource).drop 224).take 32 :=
  placementLeaf224.trans (NumericQueryFrameChecks.window_binding placementSource 224 32 (by decide +kernel))

numeric_data_binding placementLeaf256 : (data.placement.toList.drop 256).take 28 =
  NumericQueryFrameChecks.window placementSource 256 28 (by decide +kernel)

theorem placementSlice256 : (data.placement.toList.drop 256).take 28 = ((List.ofFn placementSource).drop 256).take 28 :=
  placementLeaf256.trans (NumericQueryFrameChecks.window_binding placementSource 256 28 (by decide +kernel))

theorem placementNode0_64 : (data.placement.toList.drop 0).take 64 = ((List.ofFn placementSource).drop 0).take 64 :=
  NumericQueryFrameChecks.merge_bindings data.placement.toList (List.ofFn placementSource) 0 32 32 placementSlice0 placementSlice32

theorem placementNode64_64 : (data.placement.toList.drop 64).take 64 = ((List.ofFn placementSource).drop 64).take 64 :=
  NumericQueryFrameChecks.merge_bindings data.placement.toList (List.ofFn placementSource) 64 32 32 placementSlice64 placementSlice96

theorem placementNode0_128 : (data.placement.toList.drop 0).take 128 = ((List.ofFn placementSource).drop 0).take 128 :=
  NumericQueryFrameChecks.merge_bindings data.placement.toList (List.ofFn placementSource) 0 64 64 placementNode0_64 placementNode64_64

theorem placementNode128_64 : (data.placement.toList.drop 128).take 64 = ((List.ofFn placementSource).drop 128).take 64 :=
  NumericQueryFrameChecks.merge_bindings data.placement.toList (List.ofFn placementSource) 128 32 32 placementSlice128 placementSlice160

theorem placementNode224_60 : (data.placement.toList.drop 224).take 60 = ((List.ofFn placementSource).drop 224).take 60 :=
  NumericQueryFrameChecks.merge_bindings data.placement.toList (List.ofFn placementSource) 224 32 28 placementSlice224 placementSlice256

theorem placementNode192_92 : (data.placement.toList.drop 192).take 92 = ((List.ofFn placementSource).drop 192).take 92 :=
  NumericQueryFrameChecks.merge_bindings data.placement.toList (List.ofFn placementSource) 192 32 60 placementSlice192 placementNode224_60

theorem placementNode128_156 : (data.placement.toList.drop 128).take 156 = ((List.ofFn placementSource).drop 128).take 156 :=
  NumericQueryFrameChecks.merge_bindings data.placement.toList (List.ofFn placementSource) 128 64 92 placementNode128_64 placementNode192_92

theorem placementNode0_284 : (data.placement.toList.drop 0).take 284 = ((List.ofFn placementSource).drop 0).take 284 :=
  NumericQueryFrameChecks.merge_bindings data.placement.toList (List.ofFn placementSource) 0 128 156 placementNode0_128 placementNode128_156

theorem placement_fast_binding : data.placement.toList = (List.ofFn placementSource) :=
  NumericQueryFrameChecks.complete_binding data.placement.toList (List.ofFn placementSource) 284
    (by decide +kernel) List.length_ofFn placementNode0_284

end Airbender.Compiler.MemoryFrameChecks.BigintUncached
