import Airbender.Proofs.GKRProtocol.MemoryFrameChecks.BlakeRoundUncached.Data
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.MemoryFrameChecks.BlakeRoundUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def fullAddressSource : Fin 771 → Nat := (fun wire : Fin 771 => if wire.val < 763 then AddressUniqueChecks.addressCode (Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank.address wire) else AddressUniqueChecks.addressCode (Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.bank.placement (Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank.address wire))))

numeric_data_binding fullAddressLeaf0 : (data.fullAddress.toList.drop 0).take 32 =
  NumericQueryFrameChecks.window fullAddressSource 0 32 (by decide +kernel)

theorem fullAddressSlice0 : (data.fullAddress.toList.drop 0).take 32 = ((List.ofFn fullAddressSource).drop 0).take 32 :=
  fullAddressLeaf0.trans (NumericQueryFrameChecks.window_binding fullAddressSource 0 32 (by decide +kernel))

numeric_data_binding fullAddressLeaf32 : (data.fullAddress.toList.drop 32).take 32 =
  NumericQueryFrameChecks.window fullAddressSource 32 32 (by decide +kernel)

theorem fullAddressSlice32 : (data.fullAddress.toList.drop 32).take 32 = ((List.ofFn fullAddressSource).drop 32).take 32 :=
  fullAddressLeaf32.trans (NumericQueryFrameChecks.window_binding fullAddressSource 32 32 (by decide +kernel))

numeric_data_binding fullAddressLeaf64 : (data.fullAddress.toList.drop 64).take 32 =
  NumericQueryFrameChecks.window fullAddressSource 64 32 (by decide +kernel)

theorem fullAddressSlice64 : (data.fullAddress.toList.drop 64).take 32 = ((List.ofFn fullAddressSource).drop 64).take 32 :=
  fullAddressLeaf64.trans (NumericQueryFrameChecks.window_binding fullAddressSource 64 32 (by decide +kernel))

numeric_data_binding fullAddressLeaf96 : (data.fullAddress.toList.drop 96).take 32 =
  NumericQueryFrameChecks.window fullAddressSource 96 32 (by decide +kernel)

theorem fullAddressSlice96 : (data.fullAddress.toList.drop 96).take 32 = ((List.ofFn fullAddressSource).drop 96).take 32 :=
  fullAddressLeaf96.trans (NumericQueryFrameChecks.window_binding fullAddressSource 96 32 (by decide +kernel))

numeric_data_binding fullAddressLeaf128 : (data.fullAddress.toList.drop 128).take 32 =
  NumericQueryFrameChecks.window fullAddressSource 128 32 (by decide +kernel)

theorem fullAddressSlice128 : (data.fullAddress.toList.drop 128).take 32 = ((List.ofFn fullAddressSource).drop 128).take 32 :=
  fullAddressLeaf128.trans (NumericQueryFrameChecks.window_binding fullAddressSource 128 32 (by decide +kernel))

numeric_data_binding fullAddressLeaf160 : (data.fullAddress.toList.drop 160).take 32 =
  NumericQueryFrameChecks.window fullAddressSource 160 32 (by decide +kernel)

theorem fullAddressSlice160 : (data.fullAddress.toList.drop 160).take 32 = ((List.ofFn fullAddressSource).drop 160).take 32 :=
  fullAddressLeaf160.trans (NumericQueryFrameChecks.window_binding fullAddressSource 160 32 (by decide +kernel))

numeric_data_binding fullAddressLeaf192 : (data.fullAddress.toList.drop 192).take 32 =
  NumericQueryFrameChecks.window fullAddressSource 192 32 (by decide +kernel)

theorem fullAddressSlice192 : (data.fullAddress.toList.drop 192).take 32 = ((List.ofFn fullAddressSource).drop 192).take 32 :=
  fullAddressLeaf192.trans (NumericQueryFrameChecks.window_binding fullAddressSource 192 32 (by decide +kernel))

numeric_data_binding fullAddressLeaf224 : (data.fullAddress.toList.drop 224).take 32 =
  NumericQueryFrameChecks.window fullAddressSource 224 32 (by decide +kernel)

theorem fullAddressSlice224 : (data.fullAddress.toList.drop 224).take 32 = ((List.ofFn fullAddressSource).drop 224).take 32 :=
  fullAddressLeaf224.trans (NumericQueryFrameChecks.window_binding fullAddressSource 224 32 (by decide +kernel))

numeric_data_binding fullAddressLeaf256 : (data.fullAddress.toList.drop 256).take 32 =
  NumericQueryFrameChecks.window fullAddressSource 256 32 (by decide +kernel)

theorem fullAddressSlice256 : (data.fullAddress.toList.drop 256).take 32 = ((List.ofFn fullAddressSource).drop 256).take 32 :=
  fullAddressLeaf256.trans (NumericQueryFrameChecks.window_binding fullAddressSource 256 32 (by decide +kernel))

numeric_data_binding fullAddressLeaf288 : (data.fullAddress.toList.drop 288).take 32 =
  NumericQueryFrameChecks.window fullAddressSource 288 32 (by decide +kernel)

theorem fullAddressSlice288 : (data.fullAddress.toList.drop 288).take 32 = ((List.ofFn fullAddressSource).drop 288).take 32 :=
  fullAddressLeaf288.trans (NumericQueryFrameChecks.window_binding fullAddressSource 288 32 (by decide +kernel))

numeric_data_binding fullAddressLeaf320 : (data.fullAddress.toList.drop 320).take 32 =
  NumericQueryFrameChecks.window fullAddressSource 320 32 (by decide +kernel)

theorem fullAddressSlice320 : (data.fullAddress.toList.drop 320).take 32 = ((List.ofFn fullAddressSource).drop 320).take 32 :=
  fullAddressLeaf320.trans (NumericQueryFrameChecks.window_binding fullAddressSource 320 32 (by decide +kernel))

numeric_data_binding fullAddressLeaf352 : (data.fullAddress.toList.drop 352).take 32 =
  NumericQueryFrameChecks.window fullAddressSource 352 32 (by decide +kernel)

theorem fullAddressSlice352 : (data.fullAddress.toList.drop 352).take 32 = ((List.ofFn fullAddressSource).drop 352).take 32 :=
  fullAddressLeaf352.trans (NumericQueryFrameChecks.window_binding fullAddressSource 352 32 (by decide +kernel))

numeric_data_binding fullAddressLeaf384 : (data.fullAddress.toList.drop 384).take 32 =
  NumericQueryFrameChecks.window fullAddressSource 384 32 (by decide +kernel)

theorem fullAddressSlice384 : (data.fullAddress.toList.drop 384).take 32 = ((List.ofFn fullAddressSource).drop 384).take 32 :=
  fullAddressLeaf384.trans (NumericQueryFrameChecks.window_binding fullAddressSource 384 32 (by decide +kernel))

numeric_data_binding fullAddressLeaf416 : (data.fullAddress.toList.drop 416).take 32 =
  NumericQueryFrameChecks.window fullAddressSource 416 32 (by decide +kernel)

theorem fullAddressSlice416 : (data.fullAddress.toList.drop 416).take 32 = ((List.ofFn fullAddressSource).drop 416).take 32 :=
  fullAddressLeaf416.trans (NumericQueryFrameChecks.window_binding fullAddressSource 416 32 (by decide +kernel))

numeric_data_binding fullAddressLeaf448 : (data.fullAddress.toList.drop 448).take 32 =
  NumericQueryFrameChecks.window fullAddressSource 448 32 (by decide +kernel)

theorem fullAddressSlice448 : (data.fullAddress.toList.drop 448).take 32 = ((List.ofFn fullAddressSource).drop 448).take 32 :=
  fullAddressLeaf448.trans (NumericQueryFrameChecks.window_binding fullAddressSource 448 32 (by decide +kernel))

numeric_data_binding fullAddressLeaf480 : (data.fullAddress.toList.drop 480).take 32 =
  NumericQueryFrameChecks.window fullAddressSource 480 32 (by decide +kernel)

theorem fullAddressSlice480 : (data.fullAddress.toList.drop 480).take 32 = ((List.ofFn fullAddressSource).drop 480).take 32 :=
  fullAddressLeaf480.trans (NumericQueryFrameChecks.window_binding fullAddressSource 480 32 (by decide +kernel))

numeric_data_binding fullAddressLeaf512 : (data.fullAddress.toList.drop 512).take 32 =
  NumericQueryFrameChecks.window fullAddressSource 512 32 (by decide +kernel)

theorem fullAddressSlice512 : (data.fullAddress.toList.drop 512).take 32 = ((List.ofFn fullAddressSource).drop 512).take 32 :=
  fullAddressLeaf512.trans (NumericQueryFrameChecks.window_binding fullAddressSource 512 32 (by decide +kernel))

numeric_data_binding fullAddressLeaf544 : (data.fullAddress.toList.drop 544).take 32 =
  NumericQueryFrameChecks.window fullAddressSource 544 32 (by decide +kernel)

theorem fullAddressSlice544 : (data.fullAddress.toList.drop 544).take 32 = ((List.ofFn fullAddressSource).drop 544).take 32 :=
  fullAddressLeaf544.trans (NumericQueryFrameChecks.window_binding fullAddressSource 544 32 (by decide +kernel))

numeric_data_binding fullAddressLeaf576 : (data.fullAddress.toList.drop 576).take 32 =
  NumericQueryFrameChecks.window fullAddressSource 576 32 (by decide +kernel)

theorem fullAddressSlice576 : (data.fullAddress.toList.drop 576).take 32 = ((List.ofFn fullAddressSource).drop 576).take 32 :=
  fullAddressLeaf576.trans (NumericQueryFrameChecks.window_binding fullAddressSource 576 32 (by decide +kernel))

numeric_data_binding fullAddressLeaf608 : (data.fullAddress.toList.drop 608).take 32 =
  NumericQueryFrameChecks.window fullAddressSource 608 32 (by decide +kernel)

theorem fullAddressSlice608 : (data.fullAddress.toList.drop 608).take 32 = ((List.ofFn fullAddressSource).drop 608).take 32 :=
  fullAddressLeaf608.trans (NumericQueryFrameChecks.window_binding fullAddressSource 608 32 (by decide +kernel))

numeric_data_binding fullAddressLeaf640 : (data.fullAddress.toList.drop 640).take 32 =
  NumericQueryFrameChecks.window fullAddressSource 640 32 (by decide +kernel)

theorem fullAddressSlice640 : (data.fullAddress.toList.drop 640).take 32 = ((List.ofFn fullAddressSource).drop 640).take 32 :=
  fullAddressLeaf640.trans (NumericQueryFrameChecks.window_binding fullAddressSource 640 32 (by decide +kernel))

numeric_data_binding fullAddressLeaf672 : (data.fullAddress.toList.drop 672).take 32 =
  NumericQueryFrameChecks.window fullAddressSource 672 32 (by decide +kernel)

theorem fullAddressSlice672 : (data.fullAddress.toList.drop 672).take 32 = ((List.ofFn fullAddressSource).drop 672).take 32 :=
  fullAddressLeaf672.trans (NumericQueryFrameChecks.window_binding fullAddressSource 672 32 (by decide +kernel))

numeric_data_binding fullAddressLeaf704 : (data.fullAddress.toList.drop 704).take 32 =
  NumericQueryFrameChecks.window fullAddressSource 704 32 (by decide +kernel)

theorem fullAddressSlice704 : (data.fullAddress.toList.drop 704).take 32 = ((List.ofFn fullAddressSource).drop 704).take 32 :=
  fullAddressLeaf704.trans (NumericQueryFrameChecks.window_binding fullAddressSource 704 32 (by decide +kernel))

numeric_data_binding fullAddressLeaf736 : (data.fullAddress.toList.drop 736).take 32 =
  NumericQueryFrameChecks.window fullAddressSource 736 32 (by decide +kernel)

theorem fullAddressSlice736 : (data.fullAddress.toList.drop 736).take 32 = ((List.ofFn fullAddressSource).drop 736).take 32 :=
  fullAddressLeaf736.trans (NumericQueryFrameChecks.window_binding fullAddressSource 736 32 (by decide +kernel))

numeric_data_binding fullAddressLeaf768 : (data.fullAddress.toList.drop 768).take 3 =
  NumericQueryFrameChecks.window fullAddressSource 768 3 (by decide +kernel)

theorem fullAddressSlice768 : (data.fullAddress.toList.drop 768).take 3 = ((List.ofFn fullAddressSource).drop 768).take 3 :=
  fullAddressLeaf768.trans (NumericQueryFrameChecks.window_binding fullAddressSource 768 3 (by decide +kernel))

theorem fullAddressNode32_64 : (data.fullAddress.toList.drop 32).take 64 = ((List.ofFn fullAddressSource).drop 32).take 64 :=
  NumericQueryFrameChecks.merge_bindings data.fullAddress.toList (List.ofFn fullAddressSource) 32 32 32 fullAddressSlice32 fullAddressSlice64

theorem fullAddressNode0_96 : (data.fullAddress.toList.drop 0).take 96 = ((List.ofFn fullAddressSource).drop 0).take 96 :=
  NumericQueryFrameChecks.merge_bindings data.fullAddress.toList (List.ofFn fullAddressSource) 0 32 64 fullAddressSlice0 fullAddressNode32_64

theorem fullAddressNode128_64 : (data.fullAddress.toList.drop 128).take 64 = ((List.ofFn fullAddressSource).drop 128).take 64 :=
  NumericQueryFrameChecks.merge_bindings data.fullAddress.toList (List.ofFn fullAddressSource) 128 32 32 fullAddressSlice128 fullAddressSlice160

theorem fullAddressNode96_96 : (data.fullAddress.toList.drop 96).take 96 = ((List.ofFn fullAddressSource).drop 96).take 96 :=
  NumericQueryFrameChecks.merge_bindings data.fullAddress.toList (List.ofFn fullAddressSource) 96 32 64 fullAddressSlice96 fullAddressNode128_64

theorem fullAddressNode0_192 : (data.fullAddress.toList.drop 0).take 192 = ((List.ofFn fullAddressSource).drop 0).take 192 :=
  NumericQueryFrameChecks.merge_bindings data.fullAddress.toList (List.ofFn fullAddressSource) 0 96 96 fullAddressNode0_96 fullAddressNode96_96

theorem fullAddressNode224_64 : (data.fullAddress.toList.drop 224).take 64 = ((List.ofFn fullAddressSource).drop 224).take 64 :=
  NumericQueryFrameChecks.merge_bindings data.fullAddress.toList (List.ofFn fullAddressSource) 224 32 32 fullAddressSlice224 fullAddressSlice256

theorem fullAddressNode192_96 : (data.fullAddress.toList.drop 192).take 96 = ((List.ofFn fullAddressSource).drop 192).take 96 :=
  NumericQueryFrameChecks.merge_bindings data.fullAddress.toList (List.ofFn fullAddressSource) 192 32 64 fullAddressSlice192 fullAddressNode224_64

theorem fullAddressNode320_64 : (data.fullAddress.toList.drop 320).take 64 = ((List.ofFn fullAddressSource).drop 320).take 64 :=
  NumericQueryFrameChecks.merge_bindings data.fullAddress.toList (List.ofFn fullAddressSource) 320 32 32 fullAddressSlice320 fullAddressSlice352

theorem fullAddressNode288_96 : (data.fullAddress.toList.drop 288).take 96 = ((List.ofFn fullAddressSource).drop 288).take 96 :=
  NumericQueryFrameChecks.merge_bindings data.fullAddress.toList (List.ofFn fullAddressSource) 288 32 64 fullAddressSlice288 fullAddressNode320_64

theorem fullAddressNode192_192 : (data.fullAddress.toList.drop 192).take 192 = ((List.ofFn fullAddressSource).drop 192).take 192 :=
  NumericQueryFrameChecks.merge_bindings data.fullAddress.toList (List.ofFn fullAddressSource) 192 96 96 fullAddressNode192_96 fullAddressNode288_96

theorem fullAddressNode0_384 : (data.fullAddress.toList.drop 0).take 384 = ((List.ofFn fullAddressSource).drop 0).take 384 :=
  NumericQueryFrameChecks.merge_bindings data.fullAddress.toList (List.ofFn fullAddressSource) 0 192 192 fullAddressNode0_192 fullAddressNode192_192

theorem fullAddressNode416_64 : (data.fullAddress.toList.drop 416).take 64 = ((List.ofFn fullAddressSource).drop 416).take 64 :=
  NumericQueryFrameChecks.merge_bindings data.fullAddress.toList (List.ofFn fullAddressSource) 416 32 32 fullAddressSlice416 fullAddressSlice448

theorem fullAddressNode384_96 : (data.fullAddress.toList.drop 384).take 96 = ((List.ofFn fullAddressSource).drop 384).take 96 :=
  NumericQueryFrameChecks.merge_bindings data.fullAddress.toList (List.ofFn fullAddressSource) 384 32 64 fullAddressSlice384 fullAddressNode416_64

theorem fullAddressNode512_64 : (data.fullAddress.toList.drop 512).take 64 = ((List.ofFn fullAddressSource).drop 512).take 64 :=
  NumericQueryFrameChecks.merge_bindings data.fullAddress.toList (List.ofFn fullAddressSource) 512 32 32 fullAddressSlice512 fullAddressSlice544

theorem fullAddressNode480_96 : (data.fullAddress.toList.drop 480).take 96 = ((List.ofFn fullAddressSource).drop 480).take 96 :=
  NumericQueryFrameChecks.merge_bindings data.fullAddress.toList (List.ofFn fullAddressSource) 480 32 64 fullAddressSlice480 fullAddressNode512_64

theorem fullAddressNode384_192 : (data.fullAddress.toList.drop 384).take 192 = ((List.ofFn fullAddressSource).drop 384).take 192 :=
  NumericQueryFrameChecks.merge_bindings data.fullAddress.toList (List.ofFn fullAddressSource) 384 96 96 fullAddressNode384_96 fullAddressNode480_96

theorem fullAddressNode608_64 : (data.fullAddress.toList.drop 608).take 64 = ((List.ofFn fullAddressSource).drop 608).take 64 :=
  NumericQueryFrameChecks.merge_bindings data.fullAddress.toList (List.ofFn fullAddressSource) 608 32 32 fullAddressSlice608 fullAddressSlice640

theorem fullAddressNode576_96 : (data.fullAddress.toList.drop 576).take 96 = ((List.ofFn fullAddressSource).drop 576).take 96 :=
  NumericQueryFrameChecks.merge_bindings data.fullAddress.toList (List.ofFn fullAddressSource) 576 32 64 fullAddressSlice576 fullAddressNode608_64

theorem fullAddressNode672_64 : (data.fullAddress.toList.drop 672).take 64 = ((List.ofFn fullAddressSource).drop 672).take 64 :=
  NumericQueryFrameChecks.merge_bindings data.fullAddress.toList (List.ofFn fullAddressSource) 672 32 32 fullAddressSlice672 fullAddressSlice704

theorem fullAddressNode736_35 : (data.fullAddress.toList.drop 736).take 35 = ((List.ofFn fullAddressSource).drop 736).take 35 :=
  NumericQueryFrameChecks.merge_bindings data.fullAddress.toList (List.ofFn fullAddressSource) 736 32 3 fullAddressSlice736 fullAddressSlice768

theorem fullAddressNode672_99 : (data.fullAddress.toList.drop 672).take 99 = ((List.ofFn fullAddressSource).drop 672).take 99 :=
  NumericQueryFrameChecks.merge_bindings data.fullAddress.toList (List.ofFn fullAddressSource) 672 64 35 fullAddressNode672_64 fullAddressNode736_35

theorem fullAddressNode576_195 : (data.fullAddress.toList.drop 576).take 195 = ((List.ofFn fullAddressSource).drop 576).take 195 :=
  NumericQueryFrameChecks.merge_bindings data.fullAddress.toList (List.ofFn fullAddressSource) 576 96 99 fullAddressNode576_96 fullAddressNode672_99

theorem fullAddressNode384_387 : (data.fullAddress.toList.drop 384).take 387 = ((List.ofFn fullAddressSource).drop 384).take 387 :=
  NumericQueryFrameChecks.merge_bindings data.fullAddress.toList (List.ofFn fullAddressSource) 384 192 195 fullAddressNode384_192 fullAddressNode576_195

theorem fullAddressNode0_771 : (data.fullAddress.toList.drop 0).take 771 = ((List.ofFn fullAddressSource).drop 0).take 771 :=
  NumericQueryFrameChecks.merge_bindings data.fullAddress.toList (List.ofFn fullAddressSource) 0 384 387 fullAddressNode0_384 fullAddressNode384_387

theorem fullAddress_fast_binding : data.fullAddress.toList = (List.ofFn fullAddressSource) :=
  NumericQueryFrameChecks.complete_binding data.fullAddress.toList (List.ofFn fullAddressSource) 771
    (by decide +kernel) List.length_ofFn fullAddressNode0_771

end Airbender.Compiler.MemoryFrameChecks.BlakeRoundUncached
