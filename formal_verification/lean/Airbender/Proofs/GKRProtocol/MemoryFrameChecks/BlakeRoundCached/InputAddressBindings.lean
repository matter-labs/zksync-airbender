import Airbender.Proofs.GKRProtocol.MemoryFrameChecks.BlakeRoundCached.Data
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.MemoryFrameChecks.BlakeRoundCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def inputAddressSource : Fin 771 → Nat := (fun wire : Fin 771 => if wire.val < 763 then AddressUniqueChecks.addressCode (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank.address wire) else AddressUniqueChecks.addressCode (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.inputBank.address (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.inputBank.placement (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank.address wire))))

numeric_data_binding inputAddressLeaf0 : (data.inputAddress.toList.drop 0).take 32 =
  NumericQueryFrameChecks.window inputAddressSource 0 32 (by decide +kernel)

theorem inputAddressSlice0 : (data.inputAddress.toList.drop 0).take 32 = ((List.ofFn inputAddressSource).drop 0).take 32 :=
  inputAddressLeaf0.trans (NumericQueryFrameChecks.window_binding inputAddressSource 0 32 (by decide +kernel))

numeric_data_binding inputAddressLeaf32 : (data.inputAddress.toList.drop 32).take 32 =
  NumericQueryFrameChecks.window inputAddressSource 32 32 (by decide +kernel)

theorem inputAddressSlice32 : (data.inputAddress.toList.drop 32).take 32 = ((List.ofFn inputAddressSource).drop 32).take 32 :=
  inputAddressLeaf32.trans (NumericQueryFrameChecks.window_binding inputAddressSource 32 32 (by decide +kernel))

numeric_data_binding inputAddressLeaf64 : (data.inputAddress.toList.drop 64).take 32 =
  NumericQueryFrameChecks.window inputAddressSource 64 32 (by decide +kernel)

theorem inputAddressSlice64 : (data.inputAddress.toList.drop 64).take 32 = ((List.ofFn inputAddressSource).drop 64).take 32 :=
  inputAddressLeaf64.trans (NumericQueryFrameChecks.window_binding inputAddressSource 64 32 (by decide +kernel))

numeric_data_binding inputAddressLeaf96 : (data.inputAddress.toList.drop 96).take 32 =
  NumericQueryFrameChecks.window inputAddressSource 96 32 (by decide +kernel)

theorem inputAddressSlice96 : (data.inputAddress.toList.drop 96).take 32 = ((List.ofFn inputAddressSource).drop 96).take 32 :=
  inputAddressLeaf96.trans (NumericQueryFrameChecks.window_binding inputAddressSource 96 32 (by decide +kernel))

numeric_data_binding inputAddressLeaf128 : (data.inputAddress.toList.drop 128).take 32 =
  NumericQueryFrameChecks.window inputAddressSource 128 32 (by decide +kernel)

theorem inputAddressSlice128 : (data.inputAddress.toList.drop 128).take 32 = ((List.ofFn inputAddressSource).drop 128).take 32 :=
  inputAddressLeaf128.trans (NumericQueryFrameChecks.window_binding inputAddressSource 128 32 (by decide +kernel))

numeric_data_binding inputAddressLeaf160 : (data.inputAddress.toList.drop 160).take 32 =
  NumericQueryFrameChecks.window inputAddressSource 160 32 (by decide +kernel)

theorem inputAddressSlice160 : (data.inputAddress.toList.drop 160).take 32 = ((List.ofFn inputAddressSource).drop 160).take 32 :=
  inputAddressLeaf160.trans (NumericQueryFrameChecks.window_binding inputAddressSource 160 32 (by decide +kernel))

numeric_data_binding inputAddressLeaf192 : (data.inputAddress.toList.drop 192).take 32 =
  NumericQueryFrameChecks.window inputAddressSource 192 32 (by decide +kernel)

theorem inputAddressSlice192 : (data.inputAddress.toList.drop 192).take 32 = ((List.ofFn inputAddressSource).drop 192).take 32 :=
  inputAddressLeaf192.trans (NumericQueryFrameChecks.window_binding inputAddressSource 192 32 (by decide +kernel))

numeric_data_binding inputAddressLeaf224 : (data.inputAddress.toList.drop 224).take 32 =
  NumericQueryFrameChecks.window inputAddressSource 224 32 (by decide +kernel)

theorem inputAddressSlice224 : (data.inputAddress.toList.drop 224).take 32 = ((List.ofFn inputAddressSource).drop 224).take 32 :=
  inputAddressLeaf224.trans (NumericQueryFrameChecks.window_binding inputAddressSource 224 32 (by decide +kernel))

numeric_data_binding inputAddressLeaf256 : (data.inputAddress.toList.drop 256).take 32 =
  NumericQueryFrameChecks.window inputAddressSource 256 32 (by decide +kernel)

theorem inputAddressSlice256 : (data.inputAddress.toList.drop 256).take 32 = ((List.ofFn inputAddressSource).drop 256).take 32 :=
  inputAddressLeaf256.trans (NumericQueryFrameChecks.window_binding inputAddressSource 256 32 (by decide +kernel))

numeric_data_binding inputAddressLeaf288 : (data.inputAddress.toList.drop 288).take 32 =
  NumericQueryFrameChecks.window inputAddressSource 288 32 (by decide +kernel)

theorem inputAddressSlice288 : (data.inputAddress.toList.drop 288).take 32 = ((List.ofFn inputAddressSource).drop 288).take 32 :=
  inputAddressLeaf288.trans (NumericQueryFrameChecks.window_binding inputAddressSource 288 32 (by decide +kernel))

numeric_data_binding inputAddressLeaf320 : (data.inputAddress.toList.drop 320).take 32 =
  NumericQueryFrameChecks.window inputAddressSource 320 32 (by decide +kernel)

theorem inputAddressSlice320 : (data.inputAddress.toList.drop 320).take 32 = ((List.ofFn inputAddressSource).drop 320).take 32 :=
  inputAddressLeaf320.trans (NumericQueryFrameChecks.window_binding inputAddressSource 320 32 (by decide +kernel))

numeric_data_binding inputAddressLeaf352 : (data.inputAddress.toList.drop 352).take 32 =
  NumericQueryFrameChecks.window inputAddressSource 352 32 (by decide +kernel)

theorem inputAddressSlice352 : (data.inputAddress.toList.drop 352).take 32 = ((List.ofFn inputAddressSource).drop 352).take 32 :=
  inputAddressLeaf352.trans (NumericQueryFrameChecks.window_binding inputAddressSource 352 32 (by decide +kernel))

numeric_data_binding inputAddressLeaf384 : (data.inputAddress.toList.drop 384).take 32 =
  NumericQueryFrameChecks.window inputAddressSource 384 32 (by decide +kernel)

theorem inputAddressSlice384 : (data.inputAddress.toList.drop 384).take 32 = ((List.ofFn inputAddressSource).drop 384).take 32 :=
  inputAddressLeaf384.trans (NumericQueryFrameChecks.window_binding inputAddressSource 384 32 (by decide +kernel))

numeric_data_binding inputAddressLeaf416 : (data.inputAddress.toList.drop 416).take 32 =
  NumericQueryFrameChecks.window inputAddressSource 416 32 (by decide +kernel)

theorem inputAddressSlice416 : (data.inputAddress.toList.drop 416).take 32 = ((List.ofFn inputAddressSource).drop 416).take 32 :=
  inputAddressLeaf416.trans (NumericQueryFrameChecks.window_binding inputAddressSource 416 32 (by decide +kernel))

numeric_data_binding inputAddressLeaf448 : (data.inputAddress.toList.drop 448).take 32 =
  NumericQueryFrameChecks.window inputAddressSource 448 32 (by decide +kernel)

theorem inputAddressSlice448 : (data.inputAddress.toList.drop 448).take 32 = ((List.ofFn inputAddressSource).drop 448).take 32 :=
  inputAddressLeaf448.trans (NumericQueryFrameChecks.window_binding inputAddressSource 448 32 (by decide +kernel))

numeric_data_binding inputAddressLeaf480 : (data.inputAddress.toList.drop 480).take 32 =
  NumericQueryFrameChecks.window inputAddressSource 480 32 (by decide +kernel)

theorem inputAddressSlice480 : (data.inputAddress.toList.drop 480).take 32 = ((List.ofFn inputAddressSource).drop 480).take 32 :=
  inputAddressLeaf480.trans (NumericQueryFrameChecks.window_binding inputAddressSource 480 32 (by decide +kernel))

numeric_data_binding inputAddressLeaf512 : (data.inputAddress.toList.drop 512).take 32 =
  NumericQueryFrameChecks.window inputAddressSource 512 32 (by decide +kernel)

theorem inputAddressSlice512 : (data.inputAddress.toList.drop 512).take 32 = ((List.ofFn inputAddressSource).drop 512).take 32 :=
  inputAddressLeaf512.trans (NumericQueryFrameChecks.window_binding inputAddressSource 512 32 (by decide +kernel))

numeric_data_binding inputAddressLeaf544 : (data.inputAddress.toList.drop 544).take 32 =
  NumericQueryFrameChecks.window inputAddressSource 544 32 (by decide +kernel)

theorem inputAddressSlice544 : (data.inputAddress.toList.drop 544).take 32 = ((List.ofFn inputAddressSource).drop 544).take 32 :=
  inputAddressLeaf544.trans (NumericQueryFrameChecks.window_binding inputAddressSource 544 32 (by decide +kernel))

numeric_data_binding inputAddressLeaf576 : (data.inputAddress.toList.drop 576).take 32 =
  NumericQueryFrameChecks.window inputAddressSource 576 32 (by decide +kernel)

theorem inputAddressSlice576 : (data.inputAddress.toList.drop 576).take 32 = ((List.ofFn inputAddressSource).drop 576).take 32 :=
  inputAddressLeaf576.trans (NumericQueryFrameChecks.window_binding inputAddressSource 576 32 (by decide +kernel))

numeric_data_binding inputAddressLeaf608 : (data.inputAddress.toList.drop 608).take 32 =
  NumericQueryFrameChecks.window inputAddressSource 608 32 (by decide +kernel)

theorem inputAddressSlice608 : (data.inputAddress.toList.drop 608).take 32 = ((List.ofFn inputAddressSource).drop 608).take 32 :=
  inputAddressLeaf608.trans (NumericQueryFrameChecks.window_binding inputAddressSource 608 32 (by decide +kernel))

numeric_data_binding inputAddressLeaf640 : (data.inputAddress.toList.drop 640).take 32 =
  NumericQueryFrameChecks.window inputAddressSource 640 32 (by decide +kernel)

theorem inputAddressSlice640 : (data.inputAddress.toList.drop 640).take 32 = ((List.ofFn inputAddressSource).drop 640).take 32 :=
  inputAddressLeaf640.trans (NumericQueryFrameChecks.window_binding inputAddressSource 640 32 (by decide +kernel))

numeric_data_binding inputAddressLeaf672 : (data.inputAddress.toList.drop 672).take 32 =
  NumericQueryFrameChecks.window inputAddressSource 672 32 (by decide +kernel)

theorem inputAddressSlice672 : (data.inputAddress.toList.drop 672).take 32 = ((List.ofFn inputAddressSource).drop 672).take 32 :=
  inputAddressLeaf672.trans (NumericQueryFrameChecks.window_binding inputAddressSource 672 32 (by decide +kernel))

numeric_data_binding inputAddressLeaf704 : (data.inputAddress.toList.drop 704).take 32 =
  NumericQueryFrameChecks.window inputAddressSource 704 32 (by decide +kernel)

theorem inputAddressSlice704 : (data.inputAddress.toList.drop 704).take 32 = ((List.ofFn inputAddressSource).drop 704).take 32 :=
  inputAddressLeaf704.trans (NumericQueryFrameChecks.window_binding inputAddressSource 704 32 (by decide +kernel))

numeric_data_binding inputAddressLeaf736 : (data.inputAddress.toList.drop 736).take 32 =
  NumericQueryFrameChecks.window inputAddressSource 736 32 (by decide +kernel)

theorem inputAddressSlice736 : (data.inputAddress.toList.drop 736).take 32 = ((List.ofFn inputAddressSource).drop 736).take 32 :=
  inputAddressLeaf736.trans (NumericQueryFrameChecks.window_binding inputAddressSource 736 32 (by decide +kernel))

numeric_data_binding inputAddressLeaf768 : (data.inputAddress.toList.drop 768).take 3 =
  NumericQueryFrameChecks.window inputAddressSource 768 3 (by decide +kernel)

theorem inputAddressSlice768 : (data.inputAddress.toList.drop 768).take 3 = ((List.ofFn inputAddressSource).drop 768).take 3 :=
  inputAddressLeaf768.trans (NumericQueryFrameChecks.window_binding inputAddressSource 768 3 (by decide +kernel))

theorem inputAddressNode32_64 : (data.inputAddress.toList.drop 32).take 64 = ((List.ofFn inputAddressSource).drop 32).take 64 :=
  NumericQueryFrameChecks.merge_bindings data.inputAddress.toList (List.ofFn inputAddressSource) 32 32 32 inputAddressSlice32 inputAddressSlice64

theorem inputAddressNode0_96 : (data.inputAddress.toList.drop 0).take 96 = ((List.ofFn inputAddressSource).drop 0).take 96 :=
  NumericQueryFrameChecks.merge_bindings data.inputAddress.toList (List.ofFn inputAddressSource) 0 32 64 inputAddressSlice0 inputAddressNode32_64

theorem inputAddressNode128_64 : (data.inputAddress.toList.drop 128).take 64 = ((List.ofFn inputAddressSource).drop 128).take 64 :=
  NumericQueryFrameChecks.merge_bindings data.inputAddress.toList (List.ofFn inputAddressSource) 128 32 32 inputAddressSlice128 inputAddressSlice160

theorem inputAddressNode96_96 : (data.inputAddress.toList.drop 96).take 96 = ((List.ofFn inputAddressSource).drop 96).take 96 :=
  NumericQueryFrameChecks.merge_bindings data.inputAddress.toList (List.ofFn inputAddressSource) 96 32 64 inputAddressSlice96 inputAddressNode128_64

theorem inputAddressNode0_192 : (data.inputAddress.toList.drop 0).take 192 = ((List.ofFn inputAddressSource).drop 0).take 192 :=
  NumericQueryFrameChecks.merge_bindings data.inputAddress.toList (List.ofFn inputAddressSource) 0 96 96 inputAddressNode0_96 inputAddressNode96_96

theorem inputAddressNode224_64 : (data.inputAddress.toList.drop 224).take 64 = ((List.ofFn inputAddressSource).drop 224).take 64 :=
  NumericQueryFrameChecks.merge_bindings data.inputAddress.toList (List.ofFn inputAddressSource) 224 32 32 inputAddressSlice224 inputAddressSlice256

theorem inputAddressNode192_96 : (data.inputAddress.toList.drop 192).take 96 = ((List.ofFn inputAddressSource).drop 192).take 96 :=
  NumericQueryFrameChecks.merge_bindings data.inputAddress.toList (List.ofFn inputAddressSource) 192 32 64 inputAddressSlice192 inputAddressNode224_64

theorem inputAddressNode320_64 : (data.inputAddress.toList.drop 320).take 64 = ((List.ofFn inputAddressSource).drop 320).take 64 :=
  NumericQueryFrameChecks.merge_bindings data.inputAddress.toList (List.ofFn inputAddressSource) 320 32 32 inputAddressSlice320 inputAddressSlice352

theorem inputAddressNode288_96 : (data.inputAddress.toList.drop 288).take 96 = ((List.ofFn inputAddressSource).drop 288).take 96 :=
  NumericQueryFrameChecks.merge_bindings data.inputAddress.toList (List.ofFn inputAddressSource) 288 32 64 inputAddressSlice288 inputAddressNode320_64

theorem inputAddressNode192_192 : (data.inputAddress.toList.drop 192).take 192 = ((List.ofFn inputAddressSource).drop 192).take 192 :=
  NumericQueryFrameChecks.merge_bindings data.inputAddress.toList (List.ofFn inputAddressSource) 192 96 96 inputAddressNode192_96 inputAddressNode288_96

theorem inputAddressNode0_384 : (data.inputAddress.toList.drop 0).take 384 = ((List.ofFn inputAddressSource).drop 0).take 384 :=
  NumericQueryFrameChecks.merge_bindings data.inputAddress.toList (List.ofFn inputAddressSource) 0 192 192 inputAddressNode0_192 inputAddressNode192_192

theorem inputAddressNode416_64 : (data.inputAddress.toList.drop 416).take 64 = ((List.ofFn inputAddressSource).drop 416).take 64 :=
  NumericQueryFrameChecks.merge_bindings data.inputAddress.toList (List.ofFn inputAddressSource) 416 32 32 inputAddressSlice416 inputAddressSlice448

theorem inputAddressNode384_96 : (data.inputAddress.toList.drop 384).take 96 = ((List.ofFn inputAddressSource).drop 384).take 96 :=
  NumericQueryFrameChecks.merge_bindings data.inputAddress.toList (List.ofFn inputAddressSource) 384 32 64 inputAddressSlice384 inputAddressNode416_64

theorem inputAddressNode512_64 : (data.inputAddress.toList.drop 512).take 64 = ((List.ofFn inputAddressSource).drop 512).take 64 :=
  NumericQueryFrameChecks.merge_bindings data.inputAddress.toList (List.ofFn inputAddressSource) 512 32 32 inputAddressSlice512 inputAddressSlice544

theorem inputAddressNode480_96 : (data.inputAddress.toList.drop 480).take 96 = ((List.ofFn inputAddressSource).drop 480).take 96 :=
  NumericQueryFrameChecks.merge_bindings data.inputAddress.toList (List.ofFn inputAddressSource) 480 32 64 inputAddressSlice480 inputAddressNode512_64

theorem inputAddressNode384_192 : (data.inputAddress.toList.drop 384).take 192 = ((List.ofFn inputAddressSource).drop 384).take 192 :=
  NumericQueryFrameChecks.merge_bindings data.inputAddress.toList (List.ofFn inputAddressSource) 384 96 96 inputAddressNode384_96 inputAddressNode480_96

theorem inputAddressNode608_64 : (data.inputAddress.toList.drop 608).take 64 = ((List.ofFn inputAddressSource).drop 608).take 64 :=
  NumericQueryFrameChecks.merge_bindings data.inputAddress.toList (List.ofFn inputAddressSource) 608 32 32 inputAddressSlice608 inputAddressSlice640

theorem inputAddressNode576_96 : (data.inputAddress.toList.drop 576).take 96 = ((List.ofFn inputAddressSource).drop 576).take 96 :=
  NumericQueryFrameChecks.merge_bindings data.inputAddress.toList (List.ofFn inputAddressSource) 576 32 64 inputAddressSlice576 inputAddressNode608_64

theorem inputAddressNode672_64 : (data.inputAddress.toList.drop 672).take 64 = ((List.ofFn inputAddressSource).drop 672).take 64 :=
  NumericQueryFrameChecks.merge_bindings data.inputAddress.toList (List.ofFn inputAddressSource) 672 32 32 inputAddressSlice672 inputAddressSlice704

theorem inputAddressNode736_35 : (data.inputAddress.toList.drop 736).take 35 = ((List.ofFn inputAddressSource).drop 736).take 35 :=
  NumericQueryFrameChecks.merge_bindings data.inputAddress.toList (List.ofFn inputAddressSource) 736 32 3 inputAddressSlice736 inputAddressSlice768

theorem inputAddressNode672_99 : (data.inputAddress.toList.drop 672).take 99 = ((List.ofFn inputAddressSource).drop 672).take 99 :=
  NumericQueryFrameChecks.merge_bindings data.inputAddress.toList (List.ofFn inputAddressSource) 672 64 35 inputAddressNode672_64 inputAddressNode736_35

theorem inputAddressNode576_195 : (data.inputAddress.toList.drop 576).take 195 = ((List.ofFn inputAddressSource).drop 576).take 195 :=
  NumericQueryFrameChecks.merge_bindings data.inputAddress.toList (List.ofFn inputAddressSource) 576 96 99 inputAddressNode576_96 inputAddressNode672_99

theorem inputAddressNode384_387 : (data.inputAddress.toList.drop 384).take 387 = ((List.ofFn inputAddressSource).drop 384).take 387 :=
  NumericQueryFrameChecks.merge_bindings data.inputAddress.toList (List.ofFn inputAddressSource) 384 192 195 inputAddressNode384_192 inputAddressNode576_195

theorem inputAddressNode0_771 : (data.inputAddress.toList.drop 0).take 771 = ((List.ofFn inputAddressSource).drop 0).take 771 :=
  NumericQueryFrameChecks.merge_bindings data.inputAddress.toList (List.ofFn inputAddressSource) 0 384 387 inputAddressNode0_384 inputAddressNode384_387

theorem inputAddress_fast_binding : data.inputAddress.toList = (List.ofFn inputAddressSource) :=
  NumericQueryFrameChecks.complete_binding data.inputAddress.toList (List.ofFn inputAddressSource) 771
    (by decide +kernel) List.length_ofFn inputAddressNode0_771

end Airbender.Compiler.MemoryFrameChecks.BlakeRoundCached
