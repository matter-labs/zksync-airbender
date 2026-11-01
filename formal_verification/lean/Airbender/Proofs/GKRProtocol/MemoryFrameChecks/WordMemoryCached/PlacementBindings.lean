import Airbender.Proofs.GKRProtocol.MemoryFrameChecks.WordMemoryCached.Data
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.MemoryFrameChecks.WordMemoryCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def placementSource : Fin 60 → Nat := (fun wire : Fin 60 => if wire.val < 52 then wire.val else (Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.inputBank.placement (Airbender.Compiler.MemoryNative.WordMemoryCached.native.bank.address wire)).val)

numeric_data_binding placementLeaf0 : (data.placement.toList.drop 0).take 32 =
  NumericQueryFrameChecks.window placementSource 0 32 (by decide +kernel)

theorem placementSlice0 : (data.placement.toList.drop 0).take 32 = ((List.ofFn placementSource).drop 0).take 32 :=
  placementLeaf0.trans (NumericQueryFrameChecks.window_binding placementSource 0 32 (by decide +kernel))

numeric_data_binding placementLeaf32 : (data.placement.toList.drop 32).take 28 =
  NumericQueryFrameChecks.window placementSource 32 28 (by decide +kernel)

theorem placementSlice32 : (data.placement.toList.drop 32).take 28 = ((List.ofFn placementSource).drop 32).take 28 :=
  placementLeaf32.trans (NumericQueryFrameChecks.window_binding placementSource 32 28 (by decide +kernel))

theorem placementNode0_60 : (data.placement.toList.drop 0).take 60 = ((List.ofFn placementSource).drop 0).take 60 :=
  NumericQueryFrameChecks.merge_bindings data.placement.toList (List.ofFn placementSource) 0 32 28 placementSlice0 placementSlice32

theorem placement_fast_binding : data.placement.toList = (List.ofFn placementSource) :=
  NumericQueryFrameChecks.complete_binding data.placement.toList (List.ofFn placementSource) 60
    (by decide +kernel) List.length_ofFn placementNode0_60

end Airbender.Compiler.MemoryFrameChecks.WordMemoryCached
