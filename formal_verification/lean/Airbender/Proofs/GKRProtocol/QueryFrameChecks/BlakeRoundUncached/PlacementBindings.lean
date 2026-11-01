import Airbender.Proofs.GKRProtocol.QueryFrameChecks.BlakeRoundUncached.Data
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.QueryFrameChecks.BlakeRoundUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def placementSource : Fin 638 → Nat := (fun wire : Fin 638 => (Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.inputBank.placement (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address wire)).val)

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

numeric_data_binding placementLeaf224 : (data.placement.drop 224).take 32 =
  NumericQueryFrameChecks.window placementSource 224 32 (by decide +kernel)

theorem placementSlice224 : (data.placement.drop 224).take 32 = ((List.ofFn placementSource).drop 224).take 32 :=
  placementLeaf224.trans (NumericQueryFrameChecks.window_binding placementSource 224 32 (by decide +kernel))

numeric_data_binding placementLeaf256 : (data.placement.drop 256).take 32 =
  NumericQueryFrameChecks.window placementSource 256 32 (by decide +kernel)

theorem placementSlice256 : (data.placement.drop 256).take 32 = ((List.ofFn placementSource).drop 256).take 32 :=
  placementLeaf256.trans (NumericQueryFrameChecks.window_binding placementSource 256 32 (by decide +kernel))

numeric_data_binding placementLeaf288 : (data.placement.drop 288).take 32 =
  NumericQueryFrameChecks.window placementSource 288 32 (by decide +kernel)

theorem placementSlice288 : (data.placement.drop 288).take 32 = ((List.ofFn placementSource).drop 288).take 32 :=
  placementLeaf288.trans (NumericQueryFrameChecks.window_binding placementSource 288 32 (by decide +kernel))

numeric_data_binding placementLeaf320 : (data.placement.drop 320).take 32 =
  NumericQueryFrameChecks.window placementSource 320 32 (by decide +kernel)

theorem placementSlice320 : (data.placement.drop 320).take 32 = ((List.ofFn placementSource).drop 320).take 32 :=
  placementLeaf320.trans (NumericQueryFrameChecks.window_binding placementSource 320 32 (by decide +kernel))

numeric_data_binding placementLeaf352 : (data.placement.drop 352).take 32 =
  NumericQueryFrameChecks.window placementSource 352 32 (by decide +kernel)

theorem placementSlice352 : (data.placement.drop 352).take 32 = ((List.ofFn placementSource).drop 352).take 32 :=
  placementLeaf352.trans (NumericQueryFrameChecks.window_binding placementSource 352 32 (by decide +kernel))

numeric_data_binding placementLeaf384 : (data.placement.drop 384).take 32 =
  NumericQueryFrameChecks.window placementSource 384 32 (by decide +kernel)

theorem placementSlice384 : (data.placement.drop 384).take 32 = ((List.ofFn placementSource).drop 384).take 32 :=
  placementLeaf384.trans (NumericQueryFrameChecks.window_binding placementSource 384 32 (by decide +kernel))

numeric_data_binding placementLeaf416 : (data.placement.drop 416).take 32 =
  NumericQueryFrameChecks.window placementSource 416 32 (by decide +kernel)

theorem placementSlice416 : (data.placement.drop 416).take 32 = ((List.ofFn placementSource).drop 416).take 32 :=
  placementLeaf416.trans (NumericQueryFrameChecks.window_binding placementSource 416 32 (by decide +kernel))

numeric_data_binding placementLeaf448 : (data.placement.drop 448).take 32 =
  NumericQueryFrameChecks.window placementSource 448 32 (by decide +kernel)

theorem placementSlice448 : (data.placement.drop 448).take 32 = ((List.ofFn placementSource).drop 448).take 32 :=
  placementLeaf448.trans (NumericQueryFrameChecks.window_binding placementSource 448 32 (by decide +kernel))

numeric_data_binding placementLeaf480 : (data.placement.drop 480).take 32 =
  NumericQueryFrameChecks.window placementSource 480 32 (by decide +kernel)

theorem placementSlice480 : (data.placement.drop 480).take 32 = ((List.ofFn placementSource).drop 480).take 32 :=
  placementLeaf480.trans (NumericQueryFrameChecks.window_binding placementSource 480 32 (by decide +kernel))

numeric_data_binding placementLeaf512 : (data.placement.drop 512).take 32 =
  NumericQueryFrameChecks.window placementSource 512 32 (by decide +kernel)

theorem placementSlice512 : (data.placement.drop 512).take 32 = ((List.ofFn placementSource).drop 512).take 32 :=
  placementLeaf512.trans (NumericQueryFrameChecks.window_binding placementSource 512 32 (by decide +kernel))

numeric_data_binding placementLeaf544 : (data.placement.drop 544).take 32 =
  NumericQueryFrameChecks.window placementSource 544 32 (by decide +kernel)

theorem placementSlice544 : (data.placement.drop 544).take 32 = ((List.ofFn placementSource).drop 544).take 32 :=
  placementLeaf544.trans (NumericQueryFrameChecks.window_binding placementSource 544 32 (by decide +kernel))

numeric_data_binding placementLeaf576 : (data.placement.drop 576).take 32 =
  NumericQueryFrameChecks.window placementSource 576 32 (by decide +kernel)

theorem placementSlice576 : (data.placement.drop 576).take 32 = ((List.ofFn placementSource).drop 576).take 32 :=
  placementLeaf576.trans (NumericQueryFrameChecks.window_binding placementSource 576 32 (by decide +kernel))

numeric_data_binding placementLeaf608 : (data.placement.drop 608).take 30 =
  NumericQueryFrameChecks.window placementSource 608 30 (by decide +kernel)

theorem placementSlice608 : (data.placement.drop 608).take 30 = ((List.ofFn placementSource).drop 608).take 30 :=
  placementLeaf608.trans (NumericQueryFrameChecks.window_binding placementSource 608 30 (by decide +kernel))

theorem placementNode0_64 : (data.placement.drop 0).take 64 = ((List.ofFn placementSource).drop 0).take 64 :=
  NumericQueryFrameChecks.merge_bindings data.placement (List.ofFn placementSource) 0 32 32 placementSlice0 placementSlice32

theorem placementNode96_64 : (data.placement.drop 96).take 64 = ((List.ofFn placementSource).drop 96).take 64 :=
  NumericQueryFrameChecks.merge_bindings data.placement (List.ofFn placementSource) 96 32 32 placementSlice96 placementSlice128

theorem placementNode64_96 : (data.placement.drop 64).take 96 = ((List.ofFn placementSource).drop 64).take 96 :=
  NumericQueryFrameChecks.merge_bindings data.placement (List.ofFn placementSource) 64 32 64 placementSlice64 placementNode96_64

theorem placementNode0_160 : (data.placement.drop 0).take 160 = ((List.ofFn placementSource).drop 0).take 160 :=
  NumericQueryFrameChecks.merge_bindings data.placement (List.ofFn placementSource) 0 64 96 placementNode0_64 placementNode64_96

theorem placementNode160_64 : (data.placement.drop 160).take 64 = ((List.ofFn placementSource).drop 160).take 64 :=
  NumericQueryFrameChecks.merge_bindings data.placement (List.ofFn placementSource) 160 32 32 placementSlice160 placementSlice192

theorem placementNode256_64 : (data.placement.drop 256).take 64 = ((List.ofFn placementSource).drop 256).take 64 :=
  NumericQueryFrameChecks.merge_bindings data.placement (List.ofFn placementSource) 256 32 32 placementSlice256 placementSlice288

theorem placementNode224_96 : (data.placement.drop 224).take 96 = ((List.ofFn placementSource).drop 224).take 96 :=
  NumericQueryFrameChecks.merge_bindings data.placement (List.ofFn placementSource) 224 32 64 placementSlice224 placementNode256_64

theorem placementNode160_160 : (data.placement.drop 160).take 160 = ((List.ofFn placementSource).drop 160).take 160 :=
  NumericQueryFrameChecks.merge_bindings data.placement (List.ofFn placementSource) 160 64 96 placementNode160_64 placementNode224_96

theorem placementNode0_320 : (data.placement.drop 0).take 320 = ((List.ofFn placementSource).drop 0).take 320 :=
  NumericQueryFrameChecks.merge_bindings data.placement (List.ofFn placementSource) 0 160 160 placementNode0_160 placementNode160_160

theorem placementNode320_64 : (data.placement.drop 320).take 64 = ((List.ofFn placementSource).drop 320).take 64 :=
  NumericQueryFrameChecks.merge_bindings data.placement (List.ofFn placementSource) 320 32 32 placementSlice320 placementSlice352

theorem placementNode416_64 : (data.placement.drop 416).take 64 = ((List.ofFn placementSource).drop 416).take 64 :=
  NumericQueryFrameChecks.merge_bindings data.placement (List.ofFn placementSource) 416 32 32 placementSlice416 placementSlice448

theorem placementNode384_96 : (data.placement.drop 384).take 96 = ((List.ofFn placementSource).drop 384).take 96 :=
  NumericQueryFrameChecks.merge_bindings data.placement (List.ofFn placementSource) 384 32 64 placementSlice384 placementNode416_64

theorem placementNode320_160 : (data.placement.drop 320).take 160 = ((List.ofFn placementSource).drop 320).take 160 :=
  NumericQueryFrameChecks.merge_bindings data.placement (List.ofFn placementSource) 320 64 96 placementNode320_64 placementNode384_96

theorem placementNode480_64 : (data.placement.drop 480).take 64 = ((List.ofFn placementSource).drop 480).take 64 :=
  NumericQueryFrameChecks.merge_bindings data.placement (List.ofFn placementSource) 480 32 32 placementSlice480 placementSlice512

theorem placementNode576_62 : (data.placement.drop 576).take 62 = ((List.ofFn placementSource).drop 576).take 62 :=
  NumericQueryFrameChecks.merge_bindings data.placement (List.ofFn placementSource) 576 32 30 placementSlice576 placementSlice608

theorem placementNode544_94 : (data.placement.drop 544).take 94 = ((List.ofFn placementSource).drop 544).take 94 :=
  NumericQueryFrameChecks.merge_bindings data.placement (List.ofFn placementSource) 544 32 62 placementSlice544 placementNode576_62

theorem placementNode480_158 : (data.placement.drop 480).take 158 = ((List.ofFn placementSource).drop 480).take 158 :=
  NumericQueryFrameChecks.merge_bindings data.placement (List.ofFn placementSource) 480 64 94 placementNode480_64 placementNode544_94

theorem placementNode320_318 : (data.placement.drop 320).take 318 = ((List.ofFn placementSource).drop 320).take 318 :=
  NumericQueryFrameChecks.merge_bindings data.placement (List.ofFn placementSource) 320 160 158 placementNode320_160 placementNode480_158

theorem placementNode0_638 : (data.placement.drop 0).take 638 = ((List.ofFn placementSource).drop 0).take 638 :=
  NumericQueryFrameChecks.merge_bindings data.placement (List.ofFn placementSource) 0 320 318 placementNode0_320 placementNode320_318

theorem placement_binding : data.placement = (List.ofFn placementSource) :=
  NumericQueryFrameChecks.complete_binding data.placement (List.ofFn placementSource) 638
    (by decide +kernel) (List.length_ofFn) placementNode0_638

end Airbender.Compiler.QueryFrameChecks.BlakeRoundUncached
