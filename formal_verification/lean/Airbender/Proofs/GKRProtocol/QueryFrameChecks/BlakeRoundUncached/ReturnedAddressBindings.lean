import Airbender.Proofs.GKRProtocol.QueryFrameChecks.BlakeRoundUncached.Data
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.QueryFrameChecks.BlakeRoundUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def returnedAddressSource : Fin 638 → Nat := (fun wire : Fin 638 => AddressUniqueChecks.addressCode (Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.inputBank.address (Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.inputBank.placement (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address wire))))

numeric_data_binding returnedAddressLeaf0 : (data.returnedAddress.drop 0).take 32 =
  NumericQueryFrameChecks.window returnedAddressSource 0 32 (by decide +kernel)

theorem returnedAddressSlice0 : (data.returnedAddress.drop 0).take 32 = ((List.ofFn returnedAddressSource).drop 0).take 32 :=
  returnedAddressLeaf0.trans (NumericQueryFrameChecks.window_binding returnedAddressSource 0 32 (by decide +kernel))

numeric_data_binding returnedAddressLeaf32 : (data.returnedAddress.drop 32).take 32 =
  NumericQueryFrameChecks.window returnedAddressSource 32 32 (by decide +kernel)

theorem returnedAddressSlice32 : (data.returnedAddress.drop 32).take 32 = ((List.ofFn returnedAddressSource).drop 32).take 32 :=
  returnedAddressLeaf32.trans (NumericQueryFrameChecks.window_binding returnedAddressSource 32 32 (by decide +kernel))

numeric_data_binding returnedAddressLeaf64 : (data.returnedAddress.drop 64).take 32 =
  NumericQueryFrameChecks.window returnedAddressSource 64 32 (by decide +kernel)

theorem returnedAddressSlice64 : (data.returnedAddress.drop 64).take 32 = ((List.ofFn returnedAddressSource).drop 64).take 32 :=
  returnedAddressLeaf64.trans (NumericQueryFrameChecks.window_binding returnedAddressSource 64 32 (by decide +kernel))

numeric_data_binding returnedAddressLeaf96 : (data.returnedAddress.drop 96).take 32 =
  NumericQueryFrameChecks.window returnedAddressSource 96 32 (by decide +kernel)

theorem returnedAddressSlice96 : (data.returnedAddress.drop 96).take 32 = ((List.ofFn returnedAddressSource).drop 96).take 32 :=
  returnedAddressLeaf96.trans (NumericQueryFrameChecks.window_binding returnedAddressSource 96 32 (by decide +kernel))

numeric_data_binding returnedAddressLeaf128 : (data.returnedAddress.drop 128).take 32 =
  NumericQueryFrameChecks.window returnedAddressSource 128 32 (by decide +kernel)

theorem returnedAddressSlice128 : (data.returnedAddress.drop 128).take 32 = ((List.ofFn returnedAddressSource).drop 128).take 32 :=
  returnedAddressLeaf128.trans (NumericQueryFrameChecks.window_binding returnedAddressSource 128 32 (by decide +kernel))

numeric_data_binding returnedAddressLeaf160 : (data.returnedAddress.drop 160).take 32 =
  NumericQueryFrameChecks.window returnedAddressSource 160 32 (by decide +kernel)

theorem returnedAddressSlice160 : (data.returnedAddress.drop 160).take 32 = ((List.ofFn returnedAddressSource).drop 160).take 32 :=
  returnedAddressLeaf160.trans (NumericQueryFrameChecks.window_binding returnedAddressSource 160 32 (by decide +kernel))

numeric_data_binding returnedAddressLeaf192 : (data.returnedAddress.drop 192).take 32 =
  NumericQueryFrameChecks.window returnedAddressSource 192 32 (by decide +kernel)

theorem returnedAddressSlice192 : (data.returnedAddress.drop 192).take 32 = ((List.ofFn returnedAddressSource).drop 192).take 32 :=
  returnedAddressLeaf192.trans (NumericQueryFrameChecks.window_binding returnedAddressSource 192 32 (by decide +kernel))

numeric_data_binding returnedAddressLeaf224 : (data.returnedAddress.drop 224).take 32 =
  NumericQueryFrameChecks.window returnedAddressSource 224 32 (by decide +kernel)

theorem returnedAddressSlice224 : (data.returnedAddress.drop 224).take 32 = ((List.ofFn returnedAddressSource).drop 224).take 32 :=
  returnedAddressLeaf224.trans (NumericQueryFrameChecks.window_binding returnedAddressSource 224 32 (by decide +kernel))

numeric_data_binding returnedAddressLeaf256 : (data.returnedAddress.drop 256).take 32 =
  NumericQueryFrameChecks.window returnedAddressSource 256 32 (by decide +kernel)

theorem returnedAddressSlice256 : (data.returnedAddress.drop 256).take 32 = ((List.ofFn returnedAddressSource).drop 256).take 32 :=
  returnedAddressLeaf256.trans (NumericQueryFrameChecks.window_binding returnedAddressSource 256 32 (by decide +kernel))

numeric_data_binding returnedAddressLeaf288 : (data.returnedAddress.drop 288).take 32 =
  NumericQueryFrameChecks.window returnedAddressSource 288 32 (by decide +kernel)

theorem returnedAddressSlice288 : (data.returnedAddress.drop 288).take 32 = ((List.ofFn returnedAddressSource).drop 288).take 32 :=
  returnedAddressLeaf288.trans (NumericQueryFrameChecks.window_binding returnedAddressSource 288 32 (by decide +kernel))

numeric_data_binding returnedAddressLeaf320 : (data.returnedAddress.drop 320).take 32 =
  NumericQueryFrameChecks.window returnedAddressSource 320 32 (by decide +kernel)

theorem returnedAddressSlice320 : (data.returnedAddress.drop 320).take 32 = ((List.ofFn returnedAddressSource).drop 320).take 32 :=
  returnedAddressLeaf320.trans (NumericQueryFrameChecks.window_binding returnedAddressSource 320 32 (by decide +kernel))

numeric_data_binding returnedAddressLeaf352 : (data.returnedAddress.drop 352).take 32 =
  NumericQueryFrameChecks.window returnedAddressSource 352 32 (by decide +kernel)

theorem returnedAddressSlice352 : (data.returnedAddress.drop 352).take 32 = ((List.ofFn returnedAddressSource).drop 352).take 32 :=
  returnedAddressLeaf352.trans (NumericQueryFrameChecks.window_binding returnedAddressSource 352 32 (by decide +kernel))

numeric_data_binding returnedAddressLeaf384 : (data.returnedAddress.drop 384).take 32 =
  NumericQueryFrameChecks.window returnedAddressSource 384 32 (by decide +kernel)

theorem returnedAddressSlice384 : (data.returnedAddress.drop 384).take 32 = ((List.ofFn returnedAddressSource).drop 384).take 32 :=
  returnedAddressLeaf384.trans (NumericQueryFrameChecks.window_binding returnedAddressSource 384 32 (by decide +kernel))

numeric_data_binding returnedAddressLeaf416 : (data.returnedAddress.drop 416).take 32 =
  NumericQueryFrameChecks.window returnedAddressSource 416 32 (by decide +kernel)

theorem returnedAddressSlice416 : (data.returnedAddress.drop 416).take 32 = ((List.ofFn returnedAddressSource).drop 416).take 32 :=
  returnedAddressLeaf416.trans (NumericQueryFrameChecks.window_binding returnedAddressSource 416 32 (by decide +kernel))

numeric_data_binding returnedAddressLeaf448 : (data.returnedAddress.drop 448).take 32 =
  NumericQueryFrameChecks.window returnedAddressSource 448 32 (by decide +kernel)

theorem returnedAddressSlice448 : (data.returnedAddress.drop 448).take 32 = ((List.ofFn returnedAddressSource).drop 448).take 32 :=
  returnedAddressLeaf448.trans (NumericQueryFrameChecks.window_binding returnedAddressSource 448 32 (by decide +kernel))

numeric_data_binding returnedAddressLeaf480 : (data.returnedAddress.drop 480).take 32 =
  NumericQueryFrameChecks.window returnedAddressSource 480 32 (by decide +kernel)

theorem returnedAddressSlice480 : (data.returnedAddress.drop 480).take 32 = ((List.ofFn returnedAddressSource).drop 480).take 32 :=
  returnedAddressLeaf480.trans (NumericQueryFrameChecks.window_binding returnedAddressSource 480 32 (by decide +kernel))

numeric_data_binding returnedAddressLeaf512 : (data.returnedAddress.drop 512).take 32 =
  NumericQueryFrameChecks.window returnedAddressSource 512 32 (by decide +kernel)

theorem returnedAddressSlice512 : (data.returnedAddress.drop 512).take 32 = ((List.ofFn returnedAddressSource).drop 512).take 32 :=
  returnedAddressLeaf512.trans (NumericQueryFrameChecks.window_binding returnedAddressSource 512 32 (by decide +kernel))

numeric_data_binding returnedAddressLeaf544 : (data.returnedAddress.drop 544).take 32 =
  NumericQueryFrameChecks.window returnedAddressSource 544 32 (by decide +kernel)

theorem returnedAddressSlice544 : (data.returnedAddress.drop 544).take 32 = ((List.ofFn returnedAddressSource).drop 544).take 32 :=
  returnedAddressLeaf544.trans (NumericQueryFrameChecks.window_binding returnedAddressSource 544 32 (by decide +kernel))

numeric_data_binding returnedAddressLeaf576 : (data.returnedAddress.drop 576).take 32 =
  NumericQueryFrameChecks.window returnedAddressSource 576 32 (by decide +kernel)

theorem returnedAddressSlice576 : (data.returnedAddress.drop 576).take 32 = ((List.ofFn returnedAddressSource).drop 576).take 32 :=
  returnedAddressLeaf576.trans (NumericQueryFrameChecks.window_binding returnedAddressSource 576 32 (by decide +kernel))

numeric_data_binding returnedAddressLeaf608 : (data.returnedAddress.drop 608).take 30 =
  NumericQueryFrameChecks.window returnedAddressSource 608 30 (by decide +kernel)

theorem returnedAddressSlice608 : (data.returnedAddress.drop 608).take 30 = ((List.ofFn returnedAddressSource).drop 608).take 30 :=
  returnedAddressLeaf608.trans (NumericQueryFrameChecks.window_binding returnedAddressSource 608 30 (by decide +kernel))

theorem returnedAddressNode0_64 : (data.returnedAddress.drop 0).take 64 = ((List.ofFn returnedAddressSource).drop 0).take 64 :=
  NumericQueryFrameChecks.merge_bindings data.returnedAddress (List.ofFn returnedAddressSource) 0 32 32 returnedAddressSlice0 returnedAddressSlice32

theorem returnedAddressNode96_64 : (data.returnedAddress.drop 96).take 64 = ((List.ofFn returnedAddressSource).drop 96).take 64 :=
  NumericQueryFrameChecks.merge_bindings data.returnedAddress (List.ofFn returnedAddressSource) 96 32 32 returnedAddressSlice96 returnedAddressSlice128

theorem returnedAddressNode64_96 : (data.returnedAddress.drop 64).take 96 = ((List.ofFn returnedAddressSource).drop 64).take 96 :=
  NumericQueryFrameChecks.merge_bindings data.returnedAddress (List.ofFn returnedAddressSource) 64 32 64 returnedAddressSlice64 returnedAddressNode96_64

theorem returnedAddressNode0_160 : (data.returnedAddress.drop 0).take 160 = ((List.ofFn returnedAddressSource).drop 0).take 160 :=
  NumericQueryFrameChecks.merge_bindings data.returnedAddress (List.ofFn returnedAddressSource) 0 64 96 returnedAddressNode0_64 returnedAddressNode64_96

theorem returnedAddressNode160_64 : (data.returnedAddress.drop 160).take 64 = ((List.ofFn returnedAddressSource).drop 160).take 64 :=
  NumericQueryFrameChecks.merge_bindings data.returnedAddress (List.ofFn returnedAddressSource) 160 32 32 returnedAddressSlice160 returnedAddressSlice192

theorem returnedAddressNode256_64 : (data.returnedAddress.drop 256).take 64 = ((List.ofFn returnedAddressSource).drop 256).take 64 :=
  NumericQueryFrameChecks.merge_bindings data.returnedAddress (List.ofFn returnedAddressSource) 256 32 32 returnedAddressSlice256 returnedAddressSlice288

theorem returnedAddressNode224_96 : (data.returnedAddress.drop 224).take 96 = ((List.ofFn returnedAddressSource).drop 224).take 96 :=
  NumericQueryFrameChecks.merge_bindings data.returnedAddress (List.ofFn returnedAddressSource) 224 32 64 returnedAddressSlice224 returnedAddressNode256_64

theorem returnedAddressNode160_160 : (data.returnedAddress.drop 160).take 160 = ((List.ofFn returnedAddressSource).drop 160).take 160 :=
  NumericQueryFrameChecks.merge_bindings data.returnedAddress (List.ofFn returnedAddressSource) 160 64 96 returnedAddressNode160_64 returnedAddressNode224_96

theorem returnedAddressNode0_320 : (data.returnedAddress.drop 0).take 320 = ((List.ofFn returnedAddressSource).drop 0).take 320 :=
  NumericQueryFrameChecks.merge_bindings data.returnedAddress (List.ofFn returnedAddressSource) 0 160 160 returnedAddressNode0_160 returnedAddressNode160_160

theorem returnedAddressNode320_64 : (data.returnedAddress.drop 320).take 64 = ((List.ofFn returnedAddressSource).drop 320).take 64 :=
  NumericQueryFrameChecks.merge_bindings data.returnedAddress (List.ofFn returnedAddressSource) 320 32 32 returnedAddressSlice320 returnedAddressSlice352

theorem returnedAddressNode416_64 : (data.returnedAddress.drop 416).take 64 = ((List.ofFn returnedAddressSource).drop 416).take 64 :=
  NumericQueryFrameChecks.merge_bindings data.returnedAddress (List.ofFn returnedAddressSource) 416 32 32 returnedAddressSlice416 returnedAddressSlice448

theorem returnedAddressNode384_96 : (data.returnedAddress.drop 384).take 96 = ((List.ofFn returnedAddressSource).drop 384).take 96 :=
  NumericQueryFrameChecks.merge_bindings data.returnedAddress (List.ofFn returnedAddressSource) 384 32 64 returnedAddressSlice384 returnedAddressNode416_64

theorem returnedAddressNode320_160 : (data.returnedAddress.drop 320).take 160 = ((List.ofFn returnedAddressSource).drop 320).take 160 :=
  NumericQueryFrameChecks.merge_bindings data.returnedAddress (List.ofFn returnedAddressSource) 320 64 96 returnedAddressNode320_64 returnedAddressNode384_96

theorem returnedAddressNode480_64 : (data.returnedAddress.drop 480).take 64 = ((List.ofFn returnedAddressSource).drop 480).take 64 :=
  NumericQueryFrameChecks.merge_bindings data.returnedAddress (List.ofFn returnedAddressSource) 480 32 32 returnedAddressSlice480 returnedAddressSlice512

theorem returnedAddressNode576_62 : (data.returnedAddress.drop 576).take 62 = ((List.ofFn returnedAddressSource).drop 576).take 62 :=
  NumericQueryFrameChecks.merge_bindings data.returnedAddress (List.ofFn returnedAddressSource) 576 32 30 returnedAddressSlice576 returnedAddressSlice608

theorem returnedAddressNode544_94 : (data.returnedAddress.drop 544).take 94 = ((List.ofFn returnedAddressSource).drop 544).take 94 :=
  NumericQueryFrameChecks.merge_bindings data.returnedAddress (List.ofFn returnedAddressSource) 544 32 62 returnedAddressSlice544 returnedAddressNode576_62

theorem returnedAddressNode480_158 : (data.returnedAddress.drop 480).take 158 = ((List.ofFn returnedAddressSource).drop 480).take 158 :=
  NumericQueryFrameChecks.merge_bindings data.returnedAddress (List.ofFn returnedAddressSource) 480 64 94 returnedAddressNode480_64 returnedAddressNode544_94

theorem returnedAddressNode320_318 : (data.returnedAddress.drop 320).take 318 = ((List.ofFn returnedAddressSource).drop 320).take 318 :=
  NumericQueryFrameChecks.merge_bindings data.returnedAddress (List.ofFn returnedAddressSource) 320 160 158 returnedAddressNode320_160 returnedAddressNode480_158

theorem returnedAddressNode0_638 : (data.returnedAddress.drop 0).take 638 = ((List.ofFn returnedAddressSource).drop 0).take 638 :=
  NumericQueryFrameChecks.merge_bindings data.returnedAddress (List.ofFn returnedAddressSource) 0 320 318 returnedAddressNode0_320 returnedAddressNode320_318

theorem returnedAddress_binding : data.returnedAddress = (List.ofFn returnedAddressSource) :=
  NumericQueryFrameChecks.complete_binding data.returnedAddress (List.ofFn returnedAddressSource) 638
    (by decide +kernel) (List.length_ofFn) returnedAddressNode0_638

end Airbender.Compiler.QueryFrameChecks.BlakeRoundUncached
