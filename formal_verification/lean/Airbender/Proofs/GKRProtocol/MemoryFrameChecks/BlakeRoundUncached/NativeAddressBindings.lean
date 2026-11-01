import Airbender.Proofs.GKRProtocol.MemoryFrameChecks.BlakeRoundUncached.Data
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.MemoryFrameChecks.BlakeRoundUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def nativeAddressSource : Fin 771 → Nat := (fun wire : Fin 771 => AddressUniqueChecks.addressCode (Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank.address wire))

numeric_data_binding nativeAddressLeaf0 : (data.nativeAddress.toList.drop 0).take 32 =
  NumericQueryFrameChecks.window nativeAddressSource 0 32 (by decide +kernel)

theorem nativeAddressSlice0 : (data.nativeAddress.toList.drop 0).take 32 = ((List.ofFn nativeAddressSource).drop 0).take 32 :=
  nativeAddressLeaf0.trans (NumericQueryFrameChecks.window_binding nativeAddressSource 0 32 (by decide +kernel))

numeric_data_binding nativeAddressLeaf32 : (data.nativeAddress.toList.drop 32).take 32 =
  NumericQueryFrameChecks.window nativeAddressSource 32 32 (by decide +kernel)

theorem nativeAddressSlice32 : (data.nativeAddress.toList.drop 32).take 32 = ((List.ofFn nativeAddressSource).drop 32).take 32 :=
  nativeAddressLeaf32.trans (NumericQueryFrameChecks.window_binding nativeAddressSource 32 32 (by decide +kernel))

numeric_data_binding nativeAddressLeaf64 : (data.nativeAddress.toList.drop 64).take 32 =
  NumericQueryFrameChecks.window nativeAddressSource 64 32 (by decide +kernel)

theorem nativeAddressSlice64 : (data.nativeAddress.toList.drop 64).take 32 = ((List.ofFn nativeAddressSource).drop 64).take 32 :=
  nativeAddressLeaf64.trans (NumericQueryFrameChecks.window_binding nativeAddressSource 64 32 (by decide +kernel))

numeric_data_binding nativeAddressLeaf96 : (data.nativeAddress.toList.drop 96).take 32 =
  NumericQueryFrameChecks.window nativeAddressSource 96 32 (by decide +kernel)

theorem nativeAddressSlice96 : (data.nativeAddress.toList.drop 96).take 32 = ((List.ofFn nativeAddressSource).drop 96).take 32 :=
  nativeAddressLeaf96.trans (NumericQueryFrameChecks.window_binding nativeAddressSource 96 32 (by decide +kernel))

numeric_data_binding nativeAddressLeaf128 : (data.nativeAddress.toList.drop 128).take 32 =
  NumericQueryFrameChecks.window nativeAddressSource 128 32 (by decide +kernel)

theorem nativeAddressSlice128 : (data.nativeAddress.toList.drop 128).take 32 = ((List.ofFn nativeAddressSource).drop 128).take 32 :=
  nativeAddressLeaf128.trans (NumericQueryFrameChecks.window_binding nativeAddressSource 128 32 (by decide +kernel))

numeric_data_binding nativeAddressLeaf160 : (data.nativeAddress.toList.drop 160).take 32 =
  NumericQueryFrameChecks.window nativeAddressSource 160 32 (by decide +kernel)

theorem nativeAddressSlice160 : (data.nativeAddress.toList.drop 160).take 32 = ((List.ofFn nativeAddressSource).drop 160).take 32 :=
  nativeAddressLeaf160.trans (NumericQueryFrameChecks.window_binding nativeAddressSource 160 32 (by decide +kernel))

numeric_data_binding nativeAddressLeaf192 : (data.nativeAddress.toList.drop 192).take 32 =
  NumericQueryFrameChecks.window nativeAddressSource 192 32 (by decide +kernel)

theorem nativeAddressSlice192 : (data.nativeAddress.toList.drop 192).take 32 = ((List.ofFn nativeAddressSource).drop 192).take 32 :=
  nativeAddressLeaf192.trans (NumericQueryFrameChecks.window_binding nativeAddressSource 192 32 (by decide +kernel))

numeric_data_binding nativeAddressLeaf224 : (data.nativeAddress.toList.drop 224).take 32 =
  NumericQueryFrameChecks.window nativeAddressSource 224 32 (by decide +kernel)

theorem nativeAddressSlice224 : (data.nativeAddress.toList.drop 224).take 32 = ((List.ofFn nativeAddressSource).drop 224).take 32 :=
  nativeAddressLeaf224.trans (NumericQueryFrameChecks.window_binding nativeAddressSource 224 32 (by decide +kernel))

numeric_data_binding nativeAddressLeaf256 : (data.nativeAddress.toList.drop 256).take 32 =
  NumericQueryFrameChecks.window nativeAddressSource 256 32 (by decide +kernel)

theorem nativeAddressSlice256 : (data.nativeAddress.toList.drop 256).take 32 = ((List.ofFn nativeAddressSource).drop 256).take 32 :=
  nativeAddressLeaf256.trans (NumericQueryFrameChecks.window_binding nativeAddressSource 256 32 (by decide +kernel))

numeric_data_binding nativeAddressLeaf288 : (data.nativeAddress.toList.drop 288).take 32 =
  NumericQueryFrameChecks.window nativeAddressSource 288 32 (by decide +kernel)

theorem nativeAddressSlice288 : (data.nativeAddress.toList.drop 288).take 32 = ((List.ofFn nativeAddressSource).drop 288).take 32 :=
  nativeAddressLeaf288.trans (NumericQueryFrameChecks.window_binding nativeAddressSource 288 32 (by decide +kernel))

numeric_data_binding nativeAddressLeaf320 : (data.nativeAddress.toList.drop 320).take 32 =
  NumericQueryFrameChecks.window nativeAddressSource 320 32 (by decide +kernel)

theorem nativeAddressSlice320 : (data.nativeAddress.toList.drop 320).take 32 = ((List.ofFn nativeAddressSource).drop 320).take 32 :=
  nativeAddressLeaf320.trans (NumericQueryFrameChecks.window_binding nativeAddressSource 320 32 (by decide +kernel))

numeric_data_binding nativeAddressLeaf352 : (data.nativeAddress.toList.drop 352).take 32 =
  NumericQueryFrameChecks.window nativeAddressSource 352 32 (by decide +kernel)

theorem nativeAddressSlice352 : (data.nativeAddress.toList.drop 352).take 32 = ((List.ofFn nativeAddressSource).drop 352).take 32 :=
  nativeAddressLeaf352.trans (NumericQueryFrameChecks.window_binding nativeAddressSource 352 32 (by decide +kernel))

numeric_data_binding nativeAddressLeaf384 : (data.nativeAddress.toList.drop 384).take 32 =
  NumericQueryFrameChecks.window nativeAddressSource 384 32 (by decide +kernel)

theorem nativeAddressSlice384 : (data.nativeAddress.toList.drop 384).take 32 = ((List.ofFn nativeAddressSource).drop 384).take 32 :=
  nativeAddressLeaf384.trans (NumericQueryFrameChecks.window_binding nativeAddressSource 384 32 (by decide +kernel))

numeric_data_binding nativeAddressLeaf416 : (data.nativeAddress.toList.drop 416).take 32 =
  NumericQueryFrameChecks.window nativeAddressSource 416 32 (by decide +kernel)

theorem nativeAddressSlice416 : (data.nativeAddress.toList.drop 416).take 32 = ((List.ofFn nativeAddressSource).drop 416).take 32 :=
  nativeAddressLeaf416.trans (NumericQueryFrameChecks.window_binding nativeAddressSource 416 32 (by decide +kernel))

numeric_data_binding nativeAddressLeaf448 : (data.nativeAddress.toList.drop 448).take 32 =
  NumericQueryFrameChecks.window nativeAddressSource 448 32 (by decide +kernel)

theorem nativeAddressSlice448 : (data.nativeAddress.toList.drop 448).take 32 = ((List.ofFn nativeAddressSource).drop 448).take 32 :=
  nativeAddressLeaf448.trans (NumericQueryFrameChecks.window_binding nativeAddressSource 448 32 (by decide +kernel))

numeric_data_binding nativeAddressLeaf480 : (data.nativeAddress.toList.drop 480).take 32 =
  NumericQueryFrameChecks.window nativeAddressSource 480 32 (by decide +kernel)

theorem nativeAddressSlice480 : (data.nativeAddress.toList.drop 480).take 32 = ((List.ofFn nativeAddressSource).drop 480).take 32 :=
  nativeAddressLeaf480.trans (NumericQueryFrameChecks.window_binding nativeAddressSource 480 32 (by decide +kernel))

numeric_data_binding nativeAddressLeaf512 : (data.nativeAddress.toList.drop 512).take 32 =
  NumericQueryFrameChecks.window nativeAddressSource 512 32 (by decide +kernel)

theorem nativeAddressSlice512 : (data.nativeAddress.toList.drop 512).take 32 = ((List.ofFn nativeAddressSource).drop 512).take 32 :=
  nativeAddressLeaf512.trans (NumericQueryFrameChecks.window_binding nativeAddressSource 512 32 (by decide +kernel))

numeric_data_binding nativeAddressLeaf544 : (data.nativeAddress.toList.drop 544).take 32 =
  NumericQueryFrameChecks.window nativeAddressSource 544 32 (by decide +kernel)

theorem nativeAddressSlice544 : (data.nativeAddress.toList.drop 544).take 32 = ((List.ofFn nativeAddressSource).drop 544).take 32 :=
  nativeAddressLeaf544.trans (NumericQueryFrameChecks.window_binding nativeAddressSource 544 32 (by decide +kernel))

numeric_data_binding nativeAddressLeaf576 : (data.nativeAddress.toList.drop 576).take 32 =
  NumericQueryFrameChecks.window nativeAddressSource 576 32 (by decide +kernel)

theorem nativeAddressSlice576 : (data.nativeAddress.toList.drop 576).take 32 = ((List.ofFn nativeAddressSource).drop 576).take 32 :=
  nativeAddressLeaf576.trans (NumericQueryFrameChecks.window_binding nativeAddressSource 576 32 (by decide +kernel))

numeric_data_binding nativeAddressLeaf608 : (data.nativeAddress.toList.drop 608).take 32 =
  NumericQueryFrameChecks.window nativeAddressSource 608 32 (by decide +kernel)

theorem nativeAddressSlice608 : (data.nativeAddress.toList.drop 608).take 32 = ((List.ofFn nativeAddressSource).drop 608).take 32 :=
  nativeAddressLeaf608.trans (NumericQueryFrameChecks.window_binding nativeAddressSource 608 32 (by decide +kernel))

numeric_data_binding nativeAddressLeaf640 : (data.nativeAddress.toList.drop 640).take 32 =
  NumericQueryFrameChecks.window nativeAddressSource 640 32 (by decide +kernel)

theorem nativeAddressSlice640 : (data.nativeAddress.toList.drop 640).take 32 = ((List.ofFn nativeAddressSource).drop 640).take 32 :=
  nativeAddressLeaf640.trans (NumericQueryFrameChecks.window_binding nativeAddressSource 640 32 (by decide +kernel))

numeric_data_binding nativeAddressLeaf672 : (data.nativeAddress.toList.drop 672).take 32 =
  NumericQueryFrameChecks.window nativeAddressSource 672 32 (by decide +kernel)

theorem nativeAddressSlice672 : (data.nativeAddress.toList.drop 672).take 32 = ((List.ofFn nativeAddressSource).drop 672).take 32 :=
  nativeAddressLeaf672.trans (NumericQueryFrameChecks.window_binding nativeAddressSource 672 32 (by decide +kernel))

numeric_data_binding nativeAddressLeaf704 : (data.nativeAddress.toList.drop 704).take 32 =
  NumericQueryFrameChecks.window nativeAddressSource 704 32 (by decide +kernel)

theorem nativeAddressSlice704 : (data.nativeAddress.toList.drop 704).take 32 = ((List.ofFn nativeAddressSource).drop 704).take 32 :=
  nativeAddressLeaf704.trans (NumericQueryFrameChecks.window_binding nativeAddressSource 704 32 (by decide +kernel))

numeric_data_binding nativeAddressLeaf736 : (data.nativeAddress.toList.drop 736).take 32 =
  NumericQueryFrameChecks.window nativeAddressSource 736 32 (by decide +kernel)

theorem nativeAddressSlice736 : (data.nativeAddress.toList.drop 736).take 32 = ((List.ofFn nativeAddressSource).drop 736).take 32 :=
  nativeAddressLeaf736.trans (NumericQueryFrameChecks.window_binding nativeAddressSource 736 32 (by decide +kernel))

numeric_data_binding nativeAddressLeaf768 : (data.nativeAddress.toList.drop 768).take 3 =
  NumericQueryFrameChecks.window nativeAddressSource 768 3 (by decide +kernel)

theorem nativeAddressSlice768 : (data.nativeAddress.toList.drop 768).take 3 = ((List.ofFn nativeAddressSource).drop 768).take 3 :=
  nativeAddressLeaf768.trans (NumericQueryFrameChecks.window_binding nativeAddressSource 768 3 (by decide +kernel))

theorem nativeAddressNode32_64 : (data.nativeAddress.toList.drop 32).take 64 = ((List.ofFn nativeAddressSource).drop 32).take 64 :=
  NumericQueryFrameChecks.merge_bindings data.nativeAddress.toList (List.ofFn nativeAddressSource) 32 32 32 nativeAddressSlice32 nativeAddressSlice64

theorem nativeAddressNode0_96 : (data.nativeAddress.toList.drop 0).take 96 = ((List.ofFn nativeAddressSource).drop 0).take 96 :=
  NumericQueryFrameChecks.merge_bindings data.nativeAddress.toList (List.ofFn nativeAddressSource) 0 32 64 nativeAddressSlice0 nativeAddressNode32_64

theorem nativeAddressNode128_64 : (data.nativeAddress.toList.drop 128).take 64 = ((List.ofFn nativeAddressSource).drop 128).take 64 :=
  NumericQueryFrameChecks.merge_bindings data.nativeAddress.toList (List.ofFn nativeAddressSource) 128 32 32 nativeAddressSlice128 nativeAddressSlice160

theorem nativeAddressNode96_96 : (data.nativeAddress.toList.drop 96).take 96 = ((List.ofFn nativeAddressSource).drop 96).take 96 :=
  NumericQueryFrameChecks.merge_bindings data.nativeAddress.toList (List.ofFn nativeAddressSource) 96 32 64 nativeAddressSlice96 nativeAddressNode128_64

theorem nativeAddressNode0_192 : (data.nativeAddress.toList.drop 0).take 192 = ((List.ofFn nativeAddressSource).drop 0).take 192 :=
  NumericQueryFrameChecks.merge_bindings data.nativeAddress.toList (List.ofFn nativeAddressSource) 0 96 96 nativeAddressNode0_96 nativeAddressNode96_96

theorem nativeAddressNode224_64 : (data.nativeAddress.toList.drop 224).take 64 = ((List.ofFn nativeAddressSource).drop 224).take 64 :=
  NumericQueryFrameChecks.merge_bindings data.nativeAddress.toList (List.ofFn nativeAddressSource) 224 32 32 nativeAddressSlice224 nativeAddressSlice256

theorem nativeAddressNode192_96 : (data.nativeAddress.toList.drop 192).take 96 = ((List.ofFn nativeAddressSource).drop 192).take 96 :=
  NumericQueryFrameChecks.merge_bindings data.nativeAddress.toList (List.ofFn nativeAddressSource) 192 32 64 nativeAddressSlice192 nativeAddressNode224_64

theorem nativeAddressNode320_64 : (data.nativeAddress.toList.drop 320).take 64 = ((List.ofFn nativeAddressSource).drop 320).take 64 :=
  NumericQueryFrameChecks.merge_bindings data.nativeAddress.toList (List.ofFn nativeAddressSource) 320 32 32 nativeAddressSlice320 nativeAddressSlice352

theorem nativeAddressNode288_96 : (data.nativeAddress.toList.drop 288).take 96 = ((List.ofFn nativeAddressSource).drop 288).take 96 :=
  NumericQueryFrameChecks.merge_bindings data.nativeAddress.toList (List.ofFn nativeAddressSource) 288 32 64 nativeAddressSlice288 nativeAddressNode320_64

theorem nativeAddressNode192_192 : (data.nativeAddress.toList.drop 192).take 192 = ((List.ofFn nativeAddressSource).drop 192).take 192 :=
  NumericQueryFrameChecks.merge_bindings data.nativeAddress.toList (List.ofFn nativeAddressSource) 192 96 96 nativeAddressNode192_96 nativeAddressNode288_96

theorem nativeAddressNode0_384 : (data.nativeAddress.toList.drop 0).take 384 = ((List.ofFn nativeAddressSource).drop 0).take 384 :=
  NumericQueryFrameChecks.merge_bindings data.nativeAddress.toList (List.ofFn nativeAddressSource) 0 192 192 nativeAddressNode0_192 nativeAddressNode192_192

theorem nativeAddressNode416_64 : (data.nativeAddress.toList.drop 416).take 64 = ((List.ofFn nativeAddressSource).drop 416).take 64 :=
  NumericQueryFrameChecks.merge_bindings data.nativeAddress.toList (List.ofFn nativeAddressSource) 416 32 32 nativeAddressSlice416 nativeAddressSlice448

theorem nativeAddressNode384_96 : (data.nativeAddress.toList.drop 384).take 96 = ((List.ofFn nativeAddressSource).drop 384).take 96 :=
  NumericQueryFrameChecks.merge_bindings data.nativeAddress.toList (List.ofFn nativeAddressSource) 384 32 64 nativeAddressSlice384 nativeAddressNode416_64

theorem nativeAddressNode512_64 : (data.nativeAddress.toList.drop 512).take 64 = ((List.ofFn nativeAddressSource).drop 512).take 64 :=
  NumericQueryFrameChecks.merge_bindings data.nativeAddress.toList (List.ofFn nativeAddressSource) 512 32 32 nativeAddressSlice512 nativeAddressSlice544

theorem nativeAddressNode480_96 : (data.nativeAddress.toList.drop 480).take 96 = ((List.ofFn nativeAddressSource).drop 480).take 96 :=
  NumericQueryFrameChecks.merge_bindings data.nativeAddress.toList (List.ofFn nativeAddressSource) 480 32 64 nativeAddressSlice480 nativeAddressNode512_64

theorem nativeAddressNode384_192 : (data.nativeAddress.toList.drop 384).take 192 = ((List.ofFn nativeAddressSource).drop 384).take 192 :=
  NumericQueryFrameChecks.merge_bindings data.nativeAddress.toList (List.ofFn nativeAddressSource) 384 96 96 nativeAddressNode384_96 nativeAddressNode480_96

theorem nativeAddressNode608_64 : (data.nativeAddress.toList.drop 608).take 64 = ((List.ofFn nativeAddressSource).drop 608).take 64 :=
  NumericQueryFrameChecks.merge_bindings data.nativeAddress.toList (List.ofFn nativeAddressSource) 608 32 32 nativeAddressSlice608 nativeAddressSlice640

theorem nativeAddressNode576_96 : (data.nativeAddress.toList.drop 576).take 96 = ((List.ofFn nativeAddressSource).drop 576).take 96 :=
  NumericQueryFrameChecks.merge_bindings data.nativeAddress.toList (List.ofFn nativeAddressSource) 576 32 64 nativeAddressSlice576 nativeAddressNode608_64

theorem nativeAddressNode672_64 : (data.nativeAddress.toList.drop 672).take 64 = ((List.ofFn nativeAddressSource).drop 672).take 64 :=
  NumericQueryFrameChecks.merge_bindings data.nativeAddress.toList (List.ofFn nativeAddressSource) 672 32 32 nativeAddressSlice672 nativeAddressSlice704

theorem nativeAddressNode736_35 : (data.nativeAddress.toList.drop 736).take 35 = ((List.ofFn nativeAddressSource).drop 736).take 35 :=
  NumericQueryFrameChecks.merge_bindings data.nativeAddress.toList (List.ofFn nativeAddressSource) 736 32 3 nativeAddressSlice736 nativeAddressSlice768

theorem nativeAddressNode672_99 : (data.nativeAddress.toList.drop 672).take 99 = ((List.ofFn nativeAddressSource).drop 672).take 99 :=
  NumericQueryFrameChecks.merge_bindings data.nativeAddress.toList (List.ofFn nativeAddressSource) 672 64 35 nativeAddressNode672_64 nativeAddressNode736_35

theorem nativeAddressNode576_195 : (data.nativeAddress.toList.drop 576).take 195 = ((List.ofFn nativeAddressSource).drop 576).take 195 :=
  NumericQueryFrameChecks.merge_bindings data.nativeAddress.toList (List.ofFn nativeAddressSource) 576 96 99 nativeAddressNode576_96 nativeAddressNode672_99

theorem nativeAddressNode384_387 : (data.nativeAddress.toList.drop 384).take 387 = ((List.ofFn nativeAddressSource).drop 384).take 387 :=
  NumericQueryFrameChecks.merge_bindings data.nativeAddress.toList (List.ofFn nativeAddressSource) 384 192 195 nativeAddressNode384_192 nativeAddressNode576_195

theorem nativeAddressNode0_771 : (data.nativeAddress.toList.drop 0).take 771 = ((List.ofFn nativeAddressSource).drop 0).take 771 :=
  NumericQueryFrameChecks.merge_bindings data.nativeAddress.toList (List.ofFn nativeAddressSource) 0 384 387 nativeAddressNode0_384 nativeAddressNode384_387

theorem nativeAddress_fast_binding : data.nativeAddress.toList = (List.ofFn nativeAddressSource) :=
  NumericQueryFrameChecks.complete_binding data.nativeAddress.toList (List.ofFn nativeAddressSource) 771
    (by decide +kernel) List.length_ofFn nativeAddressNode0_771

end Airbender.Compiler.MemoryFrameChecks.BlakeRoundUncached
