import Airbender.Proofs.GKRProtocol.QueryFrameChecks.BlakeRoundCached.Data
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.QueryFrameChecks.BlakeRoundCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def nativeAddressSource : Fin 638 → Nat := (fun wire : Fin 638 => AddressUniqueChecks.addressCode (Airbender.Compiler.LookupSourceNative.BlakeRoundCached.native.bank.address wire))

numeric_data_binding nativeAddressLeaf0 : (data.nativeAddress.drop 0).take 32 =
  NumericQueryFrameChecks.window nativeAddressSource 0 32 (by decide +kernel)

theorem nativeAddressSlice0 : (data.nativeAddress.drop 0).take 32 = ((List.ofFn nativeAddressSource).drop 0).take 32 :=
  nativeAddressLeaf0.trans (NumericQueryFrameChecks.window_binding nativeAddressSource 0 32 (by decide +kernel))

numeric_data_binding nativeAddressLeaf32 : (data.nativeAddress.drop 32).take 32 =
  NumericQueryFrameChecks.window nativeAddressSource 32 32 (by decide +kernel)

theorem nativeAddressSlice32 : (data.nativeAddress.drop 32).take 32 = ((List.ofFn nativeAddressSource).drop 32).take 32 :=
  nativeAddressLeaf32.trans (NumericQueryFrameChecks.window_binding nativeAddressSource 32 32 (by decide +kernel))

numeric_data_binding nativeAddressLeaf64 : (data.nativeAddress.drop 64).take 32 =
  NumericQueryFrameChecks.window nativeAddressSource 64 32 (by decide +kernel)

theorem nativeAddressSlice64 : (data.nativeAddress.drop 64).take 32 = ((List.ofFn nativeAddressSource).drop 64).take 32 :=
  nativeAddressLeaf64.trans (NumericQueryFrameChecks.window_binding nativeAddressSource 64 32 (by decide +kernel))

numeric_data_binding nativeAddressLeaf96 : (data.nativeAddress.drop 96).take 32 =
  NumericQueryFrameChecks.window nativeAddressSource 96 32 (by decide +kernel)

theorem nativeAddressSlice96 : (data.nativeAddress.drop 96).take 32 = ((List.ofFn nativeAddressSource).drop 96).take 32 :=
  nativeAddressLeaf96.trans (NumericQueryFrameChecks.window_binding nativeAddressSource 96 32 (by decide +kernel))

numeric_data_binding nativeAddressLeaf128 : (data.nativeAddress.drop 128).take 32 =
  NumericQueryFrameChecks.window nativeAddressSource 128 32 (by decide +kernel)

theorem nativeAddressSlice128 : (data.nativeAddress.drop 128).take 32 = ((List.ofFn nativeAddressSource).drop 128).take 32 :=
  nativeAddressLeaf128.trans (NumericQueryFrameChecks.window_binding nativeAddressSource 128 32 (by decide +kernel))

numeric_data_binding nativeAddressLeaf160 : (data.nativeAddress.drop 160).take 32 =
  NumericQueryFrameChecks.window nativeAddressSource 160 32 (by decide +kernel)

theorem nativeAddressSlice160 : (data.nativeAddress.drop 160).take 32 = ((List.ofFn nativeAddressSource).drop 160).take 32 :=
  nativeAddressLeaf160.trans (NumericQueryFrameChecks.window_binding nativeAddressSource 160 32 (by decide +kernel))

numeric_data_binding nativeAddressLeaf192 : (data.nativeAddress.drop 192).take 32 =
  NumericQueryFrameChecks.window nativeAddressSource 192 32 (by decide +kernel)

theorem nativeAddressSlice192 : (data.nativeAddress.drop 192).take 32 = ((List.ofFn nativeAddressSource).drop 192).take 32 :=
  nativeAddressLeaf192.trans (NumericQueryFrameChecks.window_binding nativeAddressSource 192 32 (by decide +kernel))

numeric_data_binding nativeAddressLeaf224 : (data.nativeAddress.drop 224).take 32 =
  NumericQueryFrameChecks.window nativeAddressSource 224 32 (by decide +kernel)

theorem nativeAddressSlice224 : (data.nativeAddress.drop 224).take 32 = ((List.ofFn nativeAddressSource).drop 224).take 32 :=
  nativeAddressLeaf224.trans (NumericQueryFrameChecks.window_binding nativeAddressSource 224 32 (by decide +kernel))

numeric_data_binding nativeAddressLeaf256 : (data.nativeAddress.drop 256).take 32 =
  NumericQueryFrameChecks.window nativeAddressSource 256 32 (by decide +kernel)

theorem nativeAddressSlice256 : (data.nativeAddress.drop 256).take 32 = ((List.ofFn nativeAddressSource).drop 256).take 32 :=
  nativeAddressLeaf256.trans (NumericQueryFrameChecks.window_binding nativeAddressSource 256 32 (by decide +kernel))

numeric_data_binding nativeAddressLeaf288 : (data.nativeAddress.drop 288).take 32 =
  NumericQueryFrameChecks.window nativeAddressSource 288 32 (by decide +kernel)

theorem nativeAddressSlice288 : (data.nativeAddress.drop 288).take 32 = ((List.ofFn nativeAddressSource).drop 288).take 32 :=
  nativeAddressLeaf288.trans (NumericQueryFrameChecks.window_binding nativeAddressSource 288 32 (by decide +kernel))

numeric_data_binding nativeAddressLeaf320 : (data.nativeAddress.drop 320).take 32 =
  NumericQueryFrameChecks.window nativeAddressSource 320 32 (by decide +kernel)

theorem nativeAddressSlice320 : (data.nativeAddress.drop 320).take 32 = ((List.ofFn nativeAddressSource).drop 320).take 32 :=
  nativeAddressLeaf320.trans (NumericQueryFrameChecks.window_binding nativeAddressSource 320 32 (by decide +kernel))

numeric_data_binding nativeAddressLeaf352 : (data.nativeAddress.drop 352).take 32 =
  NumericQueryFrameChecks.window nativeAddressSource 352 32 (by decide +kernel)

theorem nativeAddressSlice352 : (data.nativeAddress.drop 352).take 32 = ((List.ofFn nativeAddressSource).drop 352).take 32 :=
  nativeAddressLeaf352.trans (NumericQueryFrameChecks.window_binding nativeAddressSource 352 32 (by decide +kernel))

numeric_data_binding nativeAddressLeaf384 : (data.nativeAddress.drop 384).take 32 =
  NumericQueryFrameChecks.window nativeAddressSource 384 32 (by decide +kernel)

theorem nativeAddressSlice384 : (data.nativeAddress.drop 384).take 32 = ((List.ofFn nativeAddressSource).drop 384).take 32 :=
  nativeAddressLeaf384.trans (NumericQueryFrameChecks.window_binding nativeAddressSource 384 32 (by decide +kernel))

numeric_data_binding nativeAddressLeaf416 : (data.nativeAddress.drop 416).take 32 =
  NumericQueryFrameChecks.window nativeAddressSource 416 32 (by decide +kernel)

theorem nativeAddressSlice416 : (data.nativeAddress.drop 416).take 32 = ((List.ofFn nativeAddressSource).drop 416).take 32 :=
  nativeAddressLeaf416.trans (NumericQueryFrameChecks.window_binding nativeAddressSource 416 32 (by decide +kernel))

numeric_data_binding nativeAddressLeaf448 : (data.nativeAddress.drop 448).take 32 =
  NumericQueryFrameChecks.window nativeAddressSource 448 32 (by decide +kernel)

theorem nativeAddressSlice448 : (data.nativeAddress.drop 448).take 32 = ((List.ofFn nativeAddressSource).drop 448).take 32 :=
  nativeAddressLeaf448.trans (NumericQueryFrameChecks.window_binding nativeAddressSource 448 32 (by decide +kernel))

numeric_data_binding nativeAddressLeaf480 : (data.nativeAddress.drop 480).take 32 =
  NumericQueryFrameChecks.window nativeAddressSource 480 32 (by decide +kernel)

theorem nativeAddressSlice480 : (data.nativeAddress.drop 480).take 32 = ((List.ofFn nativeAddressSource).drop 480).take 32 :=
  nativeAddressLeaf480.trans (NumericQueryFrameChecks.window_binding nativeAddressSource 480 32 (by decide +kernel))

numeric_data_binding nativeAddressLeaf512 : (data.nativeAddress.drop 512).take 32 =
  NumericQueryFrameChecks.window nativeAddressSource 512 32 (by decide +kernel)

theorem nativeAddressSlice512 : (data.nativeAddress.drop 512).take 32 = ((List.ofFn nativeAddressSource).drop 512).take 32 :=
  nativeAddressLeaf512.trans (NumericQueryFrameChecks.window_binding nativeAddressSource 512 32 (by decide +kernel))

numeric_data_binding nativeAddressLeaf544 : (data.nativeAddress.drop 544).take 32 =
  NumericQueryFrameChecks.window nativeAddressSource 544 32 (by decide +kernel)

theorem nativeAddressSlice544 : (data.nativeAddress.drop 544).take 32 = ((List.ofFn nativeAddressSource).drop 544).take 32 :=
  nativeAddressLeaf544.trans (NumericQueryFrameChecks.window_binding nativeAddressSource 544 32 (by decide +kernel))

numeric_data_binding nativeAddressLeaf576 : (data.nativeAddress.drop 576).take 32 =
  NumericQueryFrameChecks.window nativeAddressSource 576 32 (by decide +kernel)

theorem nativeAddressSlice576 : (data.nativeAddress.drop 576).take 32 = ((List.ofFn nativeAddressSource).drop 576).take 32 :=
  nativeAddressLeaf576.trans (NumericQueryFrameChecks.window_binding nativeAddressSource 576 32 (by decide +kernel))

numeric_data_binding nativeAddressLeaf608 : (data.nativeAddress.drop 608).take 30 =
  NumericQueryFrameChecks.window nativeAddressSource 608 30 (by decide +kernel)

theorem nativeAddressSlice608 : (data.nativeAddress.drop 608).take 30 = ((List.ofFn nativeAddressSource).drop 608).take 30 :=
  nativeAddressLeaf608.trans (NumericQueryFrameChecks.window_binding nativeAddressSource 608 30 (by decide +kernel))

theorem nativeAddressNode0_64 : (data.nativeAddress.drop 0).take 64 = ((List.ofFn nativeAddressSource).drop 0).take 64 :=
  NumericQueryFrameChecks.merge_bindings data.nativeAddress (List.ofFn nativeAddressSource) 0 32 32 nativeAddressSlice0 nativeAddressSlice32

theorem nativeAddressNode96_64 : (data.nativeAddress.drop 96).take 64 = ((List.ofFn nativeAddressSource).drop 96).take 64 :=
  NumericQueryFrameChecks.merge_bindings data.nativeAddress (List.ofFn nativeAddressSource) 96 32 32 nativeAddressSlice96 nativeAddressSlice128

theorem nativeAddressNode64_96 : (data.nativeAddress.drop 64).take 96 = ((List.ofFn nativeAddressSource).drop 64).take 96 :=
  NumericQueryFrameChecks.merge_bindings data.nativeAddress (List.ofFn nativeAddressSource) 64 32 64 nativeAddressSlice64 nativeAddressNode96_64

theorem nativeAddressNode0_160 : (data.nativeAddress.drop 0).take 160 = ((List.ofFn nativeAddressSource).drop 0).take 160 :=
  NumericQueryFrameChecks.merge_bindings data.nativeAddress (List.ofFn nativeAddressSource) 0 64 96 nativeAddressNode0_64 nativeAddressNode64_96

theorem nativeAddressNode160_64 : (data.nativeAddress.drop 160).take 64 = ((List.ofFn nativeAddressSource).drop 160).take 64 :=
  NumericQueryFrameChecks.merge_bindings data.nativeAddress (List.ofFn nativeAddressSource) 160 32 32 nativeAddressSlice160 nativeAddressSlice192

theorem nativeAddressNode256_64 : (data.nativeAddress.drop 256).take 64 = ((List.ofFn nativeAddressSource).drop 256).take 64 :=
  NumericQueryFrameChecks.merge_bindings data.nativeAddress (List.ofFn nativeAddressSource) 256 32 32 nativeAddressSlice256 nativeAddressSlice288

theorem nativeAddressNode224_96 : (data.nativeAddress.drop 224).take 96 = ((List.ofFn nativeAddressSource).drop 224).take 96 :=
  NumericQueryFrameChecks.merge_bindings data.nativeAddress (List.ofFn nativeAddressSource) 224 32 64 nativeAddressSlice224 nativeAddressNode256_64

theorem nativeAddressNode160_160 : (data.nativeAddress.drop 160).take 160 = ((List.ofFn nativeAddressSource).drop 160).take 160 :=
  NumericQueryFrameChecks.merge_bindings data.nativeAddress (List.ofFn nativeAddressSource) 160 64 96 nativeAddressNode160_64 nativeAddressNode224_96

theorem nativeAddressNode0_320 : (data.nativeAddress.drop 0).take 320 = ((List.ofFn nativeAddressSource).drop 0).take 320 :=
  NumericQueryFrameChecks.merge_bindings data.nativeAddress (List.ofFn nativeAddressSource) 0 160 160 nativeAddressNode0_160 nativeAddressNode160_160

theorem nativeAddressNode320_64 : (data.nativeAddress.drop 320).take 64 = ((List.ofFn nativeAddressSource).drop 320).take 64 :=
  NumericQueryFrameChecks.merge_bindings data.nativeAddress (List.ofFn nativeAddressSource) 320 32 32 nativeAddressSlice320 nativeAddressSlice352

theorem nativeAddressNode416_64 : (data.nativeAddress.drop 416).take 64 = ((List.ofFn nativeAddressSource).drop 416).take 64 :=
  NumericQueryFrameChecks.merge_bindings data.nativeAddress (List.ofFn nativeAddressSource) 416 32 32 nativeAddressSlice416 nativeAddressSlice448

theorem nativeAddressNode384_96 : (data.nativeAddress.drop 384).take 96 = ((List.ofFn nativeAddressSource).drop 384).take 96 :=
  NumericQueryFrameChecks.merge_bindings data.nativeAddress (List.ofFn nativeAddressSource) 384 32 64 nativeAddressSlice384 nativeAddressNode416_64

theorem nativeAddressNode320_160 : (data.nativeAddress.drop 320).take 160 = ((List.ofFn nativeAddressSource).drop 320).take 160 :=
  NumericQueryFrameChecks.merge_bindings data.nativeAddress (List.ofFn nativeAddressSource) 320 64 96 nativeAddressNode320_64 nativeAddressNode384_96

theorem nativeAddressNode480_64 : (data.nativeAddress.drop 480).take 64 = ((List.ofFn nativeAddressSource).drop 480).take 64 :=
  NumericQueryFrameChecks.merge_bindings data.nativeAddress (List.ofFn nativeAddressSource) 480 32 32 nativeAddressSlice480 nativeAddressSlice512

theorem nativeAddressNode576_62 : (data.nativeAddress.drop 576).take 62 = ((List.ofFn nativeAddressSource).drop 576).take 62 :=
  NumericQueryFrameChecks.merge_bindings data.nativeAddress (List.ofFn nativeAddressSource) 576 32 30 nativeAddressSlice576 nativeAddressSlice608

theorem nativeAddressNode544_94 : (data.nativeAddress.drop 544).take 94 = ((List.ofFn nativeAddressSource).drop 544).take 94 :=
  NumericQueryFrameChecks.merge_bindings data.nativeAddress (List.ofFn nativeAddressSource) 544 32 62 nativeAddressSlice544 nativeAddressNode576_62

theorem nativeAddressNode480_158 : (data.nativeAddress.drop 480).take 158 = ((List.ofFn nativeAddressSource).drop 480).take 158 :=
  NumericQueryFrameChecks.merge_bindings data.nativeAddress (List.ofFn nativeAddressSource) 480 64 94 nativeAddressNode480_64 nativeAddressNode544_94

theorem nativeAddressNode320_318 : (data.nativeAddress.drop 320).take 318 = ((List.ofFn nativeAddressSource).drop 320).take 318 :=
  NumericQueryFrameChecks.merge_bindings data.nativeAddress (List.ofFn nativeAddressSource) 320 160 158 nativeAddressNode320_160 nativeAddressNode480_158

theorem nativeAddressNode0_638 : (data.nativeAddress.drop 0).take 638 = ((List.ofFn nativeAddressSource).drop 0).take 638 :=
  NumericQueryFrameChecks.merge_bindings data.nativeAddress (List.ofFn nativeAddressSource) 0 320 318 nativeAddressNode0_320 nativeAddressNode320_318

theorem nativeAddress_binding : data.nativeAddress = (List.ofFn nativeAddressSource) :=
  NumericQueryFrameChecks.complete_binding data.nativeAddress (List.ofFn nativeAddressSource) 638
    (by decide +kernel) (List.length_ofFn) nativeAddressNode0_638

end Airbender.Compiler.QueryFrameChecks.BlakeRoundCached
