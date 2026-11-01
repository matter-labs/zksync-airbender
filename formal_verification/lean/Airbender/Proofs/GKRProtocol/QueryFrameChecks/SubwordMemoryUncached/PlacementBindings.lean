import Airbender.Proofs.GKRProtocol.QueryFrameChecks.SubwordMemoryUncached.Data
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.QueryFrameChecks.SubwordMemoryUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def placementSource : Fin 64 → Nat := (fun wire : Fin 64 => (Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.inputBank.placement (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.address wire)).val)

numeric_data_binding placementLeaf0 : (data.placement.drop 0).take 32 =
  NumericQueryFrameChecks.window placementSource 0 32 (by decide +kernel)

theorem placementSlice0 : (data.placement.drop 0).take 32 = ((List.ofFn placementSource).drop 0).take 32 :=
  placementLeaf0.trans (NumericQueryFrameChecks.window_binding placementSource 0 32 (by decide +kernel))

numeric_data_binding placementLeaf32 : (data.placement.drop 32).take 32 =
  NumericQueryFrameChecks.window placementSource 32 32 (by decide +kernel)

theorem placementSlice32 : (data.placement.drop 32).take 32 = ((List.ofFn placementSource).drop 32).take 32 :=
  placementLeaf32.trans (NumericQueryFrameChecks.window_binding placementSource 32 32 (by decide +kernel))

theorem placementNode0_64 : (data.placement.drop 0).take 64 = ((List.ofFn placementSource).drop 0).take 64 :=
  NumericQueryFrameChecks.merge_bindings data.placement (List.ofFn placementSource) 0 32 32 placementSlice0 placementSlice32

theorem placement_binding : data.placement = (List.ofFn placementSource) :=
  NumericQueryFrameChecks.complete_binding data.placement (List.ofFn placementSource) 64
    (by decide +kernel) (List.length_ofFn) placementNode0_64

end Airbender.Compiler.QueryFrameChecks.SubwordMemoryUncached
