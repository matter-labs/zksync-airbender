import Airbender.Proofs.GKRProtocol.MemoryFrameChecks.BlakeRoundUncached.Data
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.MemoryFrameChecks.BlakeRoundUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def placementSource : Fin 771 → Nat := (fun wire : Fin 771 => if wire.val < 763 then wire.val else (Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.inputBank.placement (Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank.address wire)).val)

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

numeric_data_binding placementLeaf256 : (data.placement.toList.drop 256).take 32 =
  NumericQueryFrameChecks.window placementSource 256 32 (by decide +kernel)

theorem placementSlice256 : (data.placement.toList.drop 256).take 32 = ((List.ofFn placementSource).drop 256).take 32 :=
  placementLeaf256.trans (NumericQueryFrameChecks.window_binding placementSource 256 32 (by decide +kernel))

numeric_data_binding placementLeaf288 : (data.placement.toList.drop 288).take 32 =
  NumericQueryFrameChecks.window placementSource 288 32 (by decide +kernel)

theorem placementSlice288 : (data.placement.toList.drop 288).take 32 = ((List.ofFn placementSource).drop 288).take 32 :=
  placementLeaf288.trans (NumericQueryFrameChecks.window_binding placementSource 288 32 (by decide +kernel))

numeric_data_binding placementLeaf320 : (data.placement.toList.drop 320).take 32 =
  NumericQueryFrameChecks.window placementSource 320 32 (by decide +kernel)

theorem placementSlice320 : (data.placement.toList.drop 320).take 32 = ((List.ofFn placementSource).drop 320).take 32 :=
  placementLeaf320.trans (NumericQueryFrameChecks.window_binding placementSource 320 32 (by decide +kernel))

numeric_data_binding placementLeaf352 : (data.placement.toList.drop 352).take 32 =
  NumericQueryFrameChecks.window placementSource 352 32 (by decide +kernel)

theorem placementSlice352 : (data.placement.toList.drop 352).take 32 = ((List.ofFn placementSource).drop 352).take 32 :=
  placementLeaf352.trans (NumericQueryFrameChecks.window_binding placementSource 352 32 (by decide +kernel))

numeric_data_binding placementLeaf384 : (data.placement.toList.drop 384).take 32 =
  NumericQueryFrameChecks.window placementSource 384 32 (by decide +kernel)

theorem placementSlice384 : (data.placement.toList.drop 384).take 32 = ((List.ofFn placementSource).drop 384).take 32 :=
  placementLeaf384.trans (NumericQueryFrameChecks.window_binding placementSource 384 32 (by decide +kernel))

numeric_data_binding placementLeaf416 : (data.placement.toList.drop 416).take 32 =
  NumericQueryFrameChecks.window placementSource 416 32 (by decide +kernel)

theorem placementSlice416 : (data.placement.toList.drop 416).take 32 = ((List.ofFn placementSource).drop 416).take 32 :=
  placementLeaf416.trans (NumericQueryFrameChecks.window_binding placementSource 416 32 (by decide +kernel))

numeric_data_binding placementLeaf448 : (data.placement.toList.drop 448).take 32 =
  NumericQueryFrameChecks.window placementSource 448 32 (by decide +kernel)

theorem placementSlice448 : (data.placement.toList.drop 448).take 32 = ((List.ofFn placementSource).drop 448).take 32 :=
  placementLeaf448.trans (NumericQueryFrameChecks.window_binding placementSource 448 32 (by decide +kernel))

numeric_data_binding placementLeaf480 : (data.placement.toList.drop 480).take 32 =
  NumericQueryFrameChecks.window placementSource 480 32 (by decide +kernel)

theorem placementSlice480 : (data.placement.toList.drop 480).take 32 = ((List.ofFn placementSource).drop 480).take 32 :=
  placementLeaf480.trans (NumericQueryFrameChecks.window_binding placementSource 480 32 (by decide +kernel))

numeric_data_binding placementLeaf512 : (data.placement.toList.drop 512).take 32 =
  NumericQueryFrameChecks.window placementSource 512 32 (by decide +kernel)

theorem placementSlice512 : (data.placement.toList.drop 512).take 32 = ((List.ofFn placementSource).drop 512).take 32 :=
  placementLeaf512.trans (NumericQueryFrameChecks.window_binding placementSource 512 32 (by decide +kernel))

numeric_data_binding placementLeaf544 : (data.placement.toList.drop 544).take 32 =
  NumericQueryFrameChecks.window placementSource 544 32 (by decide +kernel)

theorem placementSlice544 : (data.placement.toList.drop 544).take 32 = ((List.ofFn placementSource).drop 544).take 32 :=
  placementLeaf544.trans (NumericQueryFrameChecks.window_binding placementSource 544 32 (by decide +kernel))

numeric_data_binding placementLeaf576 : (data.placement.toList.drop 576).take 32 =
  NumericQueryFrameChecks.window placementSource 576 32 (by decide +kernel)

theorem placementSlice576 : (data.placement.toList.drop 576).take 32 = ((List.ofFn placementSource).drop 576).take 32 :=
  placementLeaf576.trans (NumericQueryFrameChecks.window_binding placementSource 576 32 (by decide +kernel))

numeric_data_binding placementLeaf608 : (data.placement.toList.drop 608).take 32 =
  NumericQueryFrameChecks.window placementSource 608 32 (by decide +kernel)

theorem placementSlice608 : (data.placement.toList.drop 608).take 32 = ((List.ofFn placementSource).drop 608).take 32 :=
  placementLeaf608.trans (NumericQueryFrameChecks.window_binding placementSource 608 32 (by decide +kernel))

numeric_data_binding placementLeaf640 : (data.placement.toList.drop 640).take 32 =
  NumericQueryFrameChecks.window placementSource 640 32 (by decide +kernel)

theorem placementSlice640 : (data.placement.toList.drop 640).take 32 = ((List.ofFn placementSource).drop 640).take 32 :=
  placementLeaf640.trans (NumericQueryFrameChecks.window_binding placementSource 640 32 (by decide +kernel))

numeric_data_binding placementLeaf672 : (data.placement.toList.drop 672).take 32 =
  NumericQueryFrameChecks.window placementSource 672 32 (by decide +kernel)

theorem placementSlice672 : (data.placement.toList.drop 672).take 32 = ((List.ofFn placementSource).drop 672).take 32 :=
  placementLeaf672.trans (NumericQueryFrameChecks.window_binding placementSource 672 32 (by decide +kernel))

numeric_data_binding placementLeaf704 : (data.placement.toList.drop 704).take 32 =
  NumericQueryFrameChecks.window placementSource 704 32 (by decide +kernel)

theorem placementSlice704 : (data.placement.toList.drop 704).take 32 = ((List.ofFn placementSource).drop 704).take 32 :=
  placementLeaf704.trans (NumericQueryFrameChecks.window_binding placementSource 704 32 (by decide +kernel))

numeric_data_binding placementLeaf736 : (data.placement.toList.drop 736).take 32 =
  NumericQueryFrameChecks.window placementSource 736 32 (by decide +kernel)

theorem placementSlice736 : (data.placement.toList.drop 736).take 32 = ((List.ofFn placementSource).drop 736).take 32 :=
  placementLeaf736.trans (NumericQueryFrameChecks.window_binding placementSource 736 32 (by decide +kernel))

numeric_data_binding placementLeaf768 : (data.placement.toList.drop 768).take 3 =
  NumericQueryFrameChecks.window placementSource 768 3 (by decide +kernel)

theorem placementSlice768 : (data.placement.toList.drop 768).take 3 = ((List.ofFn placementSource).drop 768).take 3 :=
  placementLeaf768.trans (NumericQueryFrameChecks.window_binding placementSource 768 3 (by decide +kernel))

theorem placementNode32_64 : (data.placement.toList.drop 32).take 64 = ((List.ofFn placementSource).drop 32).take 64 :=
  NumericQueryFrameChecks.merge_bindings data.placement.toList (List.ofFn placementSource) 32 32 32 placementSlice32 placementSlice64

theorem placementNode0_96 : (data.placement.toList.drop 0).take 96 = ((List.ofFn placementSource).drop 0).take 96 :=
  NumericQueryFrameChecks.merge_bindings data.placement.toList (List.ofFn placementSource) 0 32 64 placementSlice0 placementNode32_64

theorem placementNode128_64 : (data.placement.toList.drop 128).take 64 = ((List.ofFn placementSource).drop 128).take 64 :=
  NumericQueryFrameChecks.merge_bindings data.placement.toList (List.ofFn placementSource) 128 32 32 placementSlice128 placementSlice160

theorem placementNode96_96 : (data.placement.toList.drop 96).take 96 = ((List.ofFn placementSource).drop 96).take 96 :=
  NumericQueryFrameChecks.merge_bindings data.placement.toList (List.ofFn placementSource) 96 32 64 placementSlice96 placementNode128_64

theorem placementNode0_192 : (data.placement.toList.drop 0).take 192 = ((List.ofFn placementSource).drop 0).take 192 :=
  NumericQueryFrameChecks.merge_bindings data.placement.toList (List.ofFn placementSource) 0 96 96 placementNode0_96 placementNode96_96

theorem placementNode224_64 : (data.placement.toList.drop 224).take 64 = ((List.ofFn placementSource).drop 224).take 64 :=
  NumericQueryFrameChecks.merge_bindings data.placement.toList (List.ofFn placementSource) 224 32 32 placementSlice224 placementSlice256

theorem placementNode192_96 : (data.placement.toList.drop 192).take 96 = ((List.ofFn placementSource).drop 192).take 96 :=
  NumericQueryFrameChecks.merge_bindings data.placement.toList (List.ofFn placementSource) 192 32 64 placementSlice192 placementNode224_64

theorem placementNode320_64 : (data.placement.toList.drop 320).take 64 = ((List.ofFn placementSource).drop 320).take 64 :=
  NumericQueryFrameChecks.merge_bindings data.placement.toList (List.ofFn placementSource) 320 32 32 placementSlice320 placementSlice352

theorem placementNode288_96 : (data.placement.toList.drop 288).take 96 = ((List.ofFn placementSource).drop 288).take 96 :=
  NumericQueryFrameChecks.merge_bindings data.placement.toList (List.ofFn placementSource) 288 32 64 placementSlice288 placementNode320_64

theorem placementNode192_192 : (data.placement.toList.drop 192).take 192 = ((List.ofFn placementSource).drop 192).take 192 :=
  NumericQueryFrameChecks.merge_bindings data.placement.toList (List.ofFn placementSource) 192 96 96 placementNode192_96 placementNode288_96

theorem placementNode0_384 : (data.placement.toList.drop 0).take 384 = ((List.ofFn placementSource).drop 0).take 384 :=
  NumericQueryFrameChecks.merge_bindings data.placement.toList (List.ofFn placementSource) 0 192 192 placementNode0_192 placementNode192_192

theorem placementNode416_64 : (data.placement.toList.drop 416).take 64 = ((List.ofFn placementSource).drop 416).take 64 :=
  NumericQueryFrameChecks.merge_bindings data.placement.toList (List.ofFn placementSource) 416 32 32 placementSlice416 placementSlice448

theorem placementNode384_96 : (data.placement.toList.drop 384).take 96 = ((List.ofFn placementSource).drop 384).take 96 :=
  NumericQueryFrameChecks.merge_bindings data.placement.toList (List.ofFn placementSource) 384 32 64 placementSlice384 placementNode416_64

theorem placementNode512_64 : (data.placement.toList.drop 512).take 64 = ((List.ofFn placementSource).drop 512).take 64 :=
  NumericQueryFrameChecks.merge_bindings data.placement.toList (List.ofFn placementSource) 512 32 32 placementSlice512 placementSlice544

theorem placementNode480_96 : (data.placement.toList.drop 480).take 96 = ((List.ofFn placementSource).drop 480).take 96 :=
  NumericQueryFrameChecks.merge_bindings data.placement.toList (List.ofFn placementSource) 480 32 64 placementSlice480 placementNode512_64

theorem placementNode384_192 : (data.placement.toList.drop 384).take 192 = ((List.ofFn placementSource).drop 384).take 192 :=
  NumericQueryFrameChecks.merge_bindings data.placement.toList (List.ofFn placementSource) 384 96 96 placementNode384_96 placementNode480_96

theorem placementNode608_64 : (data.placement.toList.drop 608).take 64 = ((List.ofFn placementSource).drop 608).take 64 :=
  NumericQueryFrameChecks.merge_bindings data.placement.toList (List.ofFn placementSource) 608 32 32 placementSlice608 placementSlice640

theorem placementNode576_96 : (data.placement.toList.drop 576).take 96 = ((List.ofFn placementSource).drop 576).take 96 :=
  NumericQueryFrameChecks.merge_bindings data.placement.toList (List.ofFn placementSource) 576 32 64 placementSlice576 placementNode608_64

theorem placementNode672_64 : (data.placement.toList.drop 672).take 64 = ((List.ofFn placementSource).drop 672).take 64 :=
  NumericQueryFrameChecks.merge_bindings data.placement.toList (List.ofFn placementSource) 672 32 32 placementSlice672 placementSlice704

theorem placementNode736_35 : (data.placement.toList.drop 736).take 35 = ((List.ofFn placementSource).drop 736).take 35 :=
  NumericQueryFrameChecks.merge_bindings data.placement.toList (List.ofFn placementSource) 736 32 3 placementSlice736 placementSlice768

theorem placementNode672_99 : (data.placement.toList.drop 672).take 99 = ((List.ofFn placementSource).drop 672).take 99 :=
  NumericQueryFrameChecks.merge_bindings data.placement.toList (List.ofFn placementSource) 672 64 35 placementNode672_64 placementNode736_35

theorem placementNode576_195 : (data.placement.toList.drop 576).take 195 = ((List.ofFn placementSource).drop 576).take 195 :=
  NumericQueryFrameChecks.merge_bindings data.placement.toList (List.ofFn placementSource) 576 96 99 placementNode576_96 placementNode672_99

theorem placementNode384_387 : (data.placement.toList.drop 384).take 387 = ((List.ofFn placementSource).drop 384).take 387 :=
  NumericQueryFrameChecks.merge_bindings data.placement.toList (List.ofFn placementSource) 384 192 195 placementNode384_192 placementNode576_195

theorem placementNode0_771 : (data.placement.toList.drop 0).take 771 = ((List.ofFn placementSource).drop 0).take 771 :=
  NumericQueryFrameChecks.merge_bindings data.placement.toList (List.ofFn placementSource) 0 384 387 placementNode0_384 placementNode384_387

theorem placement_fast_binding : data.placement.toList = (List.ofFn placementSource) :=
  NumericQueryFrameChecks.complete_binding data.placement.toList (List.ofFn placementSource) 771
    (by decide +kernel) List.length_ofFn placementNode0_771

end Airbender.Compiler.MemoryFrameChecks.BlakeRoundUncached
