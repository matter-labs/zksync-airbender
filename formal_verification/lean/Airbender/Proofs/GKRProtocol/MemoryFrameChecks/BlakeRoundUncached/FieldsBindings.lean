import Airbender.Proofs.GKRProtocol.MemoryFrameChecks.BlakeRoundUncached.Data
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.MemoryFrameChecks.BlakeRoundUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def encodeField : Source.MemoryField → NumericPolynomialChecks.Data := (fun field : Source.MemoryField => NumericPolynomialChecks.encode (field.polynomial Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.sourcePlacement))

noncomputable def ramSource := Airbender.Compiler.MemoryFrameNative.BlakeRoundUncached.native.ramFields.map encodeField

numeric_data_binding ramLeaf0 : (data.ram.drop 0).take 16 =
  ((Airbender.Compiler.MemoryFrameNative.BlakeRoundUncached.native.ramFields.drop 0).take 16).map encodeField

theorem ramSlice0 : (data.ram.drop 0).take 16 = (ramSource.drop 0).take 16 :=
  ramLeaf0.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryFrameNative.BlakeRoundUncached.native.ramFields encodeField 0 16)

numeric_data_binding ramLeaf16 : (data.ram.drop 16).take 16 =
  ((Airbender.Compiler.MemoryFrameNative.BlakeRoundUncached.native.ramFields.drop 16).take 16).map encodeField

theorem ramSlice16 : (data.ram.drop 16).take 16 = (ramSource.drop 16).take 16 :=
  ramLeaf16.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryFrameNative.BlakeRoundUncached.native.ramFields encodeField 16 16)

numeric_data_binding ramLeaf32 : (data.ram.drop 32).take 16 =
  ((Airbender.Compiler.MemoryFrameNative.BlakeRoundUncached.native.ramFields.drop 32).take 16).map encodeField

theorem ramSlice32 : (data.ram.drop 32).take 16 = (ramSource.drop 32).take 16 :=
  ramLeaf32.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryFrameNative.BlakeRoundUncached.native.ramFields encodeField 32 16)

numeric_data_binding ramLeaf48 : (data.ram.drop 48).take 16 =
  ((Airbender.Compiler.MemoryFrameNative.BlakeRoundUncached.native.ramFields.drop 48).take 16).map encodeField

theorem ramSlice48 : (data.ram.drop 48).take 16 = (ramSource.drop 48).take 16 :=
  ramLeaf48.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryFrameNative.BlakeRoundUncached.native.ramFields encodeField 48 16)

numeric_data_binding ramLeaf64 : (data.ram.drop 64).take 16 =
  ((Airbender.Compiler.MemoryFrameNative.BlakeRoundUncached.native.ramFields.drop 64).take 16).map encodeField

theorem ramSlice64 : (data.ram.drop 64).take 16 = (ramSource.drop 64).take 16 :=
  ramLeaf64.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryFrameNative.BlakeRoundUncached.native.ramFields encodeField 64 16)

numeric_data_binding ramLeaf80 : (data.ram.drop 80).take 16 =
  ((Airbender.Compiler.MemoryFrameNative.BlakeRoundUncached.native.ramFields.drop 80).take 16).map encodeField

theorem ramSlice80 : (data.ram.drop 80).take 16 = (ramSource.drop 80).take 16 :=
  ramLeaf80.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryFrameNative.BlakeRoundUncached.native.ramFields encodeField 80 16)

numeric_data_binding ramLeaf96 : (data.ram.drop 96).take 16 =
  ((Airbender.Compiler.MemoryFrameNative.BlakeRoundUncached.native.ramFields.drop 96).take 16).map encodeField

theorem ramSlice96 : (data.ram.drop 96).take 16 = (ramSource.drop 96).take 16 :=
  ramLeaf96.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryFrameNative.BlakeRoundUncached.native.ramFields encodeField 96 16)

numeric_data_binding ramLeaf112 : (data.ram.drop 112).take 16 =
  ((Airbender.Compiler.MemoryFrameNative.BlakeRoundUncached.native.ramFields.drop 112).take 16).map encodeField

theorem ramSlice112 : (data.ram.drop 112).take 16 = (ramSource.drop 112).take 16 :=
  ramLeaf112.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryFrameNative.BlakeRoundUncached.native.ramFields encodeField 112 16)

numeric_data_binding ramLeaf128 : (data.ram.drop 128).take 16 =
  ((Airbender.Compiler.MemoryFrameNative.BlakeRoundUncached.native.ramFields.drop 128).take 16).map encodeField

theorem ramSlice128 : (data.ram.drop 128).take 16 = (ramSource.drop 128).take 16 :=
  ramLeaf128.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryFrameNative.BlakeRoundUncached.native.ramFields encodeField 128 16)

numeric_data_binding ramLeaf144 : (data.ram.drop 144).take 16 =
  ((Airbender.Compiler.MemoryFrameNative.BlakeRoundUncached.native.ramFields.drop 144).take 16).map encodeField

theorem ramSlice144 : (data.ram.drop 144).take 16 = (ramSource.drop 144).take 16 :=
  ramLeaf144.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryFrameNative.BlakeRoundUncached.native.ramFields encodeField 144 16)

numeric_data_binding ramLeaf160 : (data.ram.drop 160).take 16 =
  ((Airbender.Compiler.MemoryFrameNative.BlakeRoundUncached.native.ramFields.drop 160).take 16).map encodeField

theorem ramSlice160 : (data.ram.drop 160).take 16 = (ramSource.drop 160).take 16 :=
  ramLeaf160.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryFrameNative.BlakeRoundUncached.native.ramFields encodeField 160 16)

numeric_data_binding ramLeaf176 : (data.ram.drop 176).take 16 =
  ((Airbender.Compiler.MemoryFrameNative.BlakeRoundUncached.native.ramFields.drop 176).take 16).map encodeField

theorem ramSlice176 : (data.ram.drop 176).take 16 = (ramSource.drop 176).take 16 :=
  ramLeaf176.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryFrameNative.BlakeRoundUncached.native.ramFields encodeField 176 16)

numeric_data_binding ramLeaf192 : (data.ram.drop 192).take 16 =
  ((Airbender.Compiler.MemoryFrameNative.BlakeRoundUncached.native.ramFields.drop 192).take 16).map encodeField

theorem ramSlice192 : (data.ram.drop 192).take 16 = (ramSource.drop 192).take 16 :=
  ramLeaf192.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryFrameNative.BlakeRoundUncached.native.ramFields encodeField 192 16)

numeric_data_binding ramLeaf208 : (data.ram.drop 208).take 16 =
  ((Airbender.Compiler.MemoryFrameNative.BlakeRoundUncached.native.ramFields.drop 208).take 16).map encodeField

theorem ramSlice208 : (data.ram.drop 208).take 16 = (ramSource.drop 208).take 16 :=
  ramLeaf208.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryFrameNative.BlakeRoundUncached.native.ramFields encodeField 208 16)

numeric_data_binding ramLeaf224 : (data.ram.drop 224).take 16 =
  ((Airbender.Compiler.MemoryFrameNative.BlakeRoundUncached.native.ramFields.drop 224).take 16).map encodeField

theorem ramSlice224 : (data.ram.drop 224).take 16 = (ramSource.drop 224).take 16 :=
  ramLeaf224.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryFrameNative.BlakeRoundUncached.native.ramFields encodeField 224 16)

numeric_data_binding ramLeaf240 : (data.ram.drop 240).take 16 =
  ((Airbender.Compiler.MemoryFrameNative.BlakeRoundUncached.native.ramFields.drop 240).take 16).map encodeField

theorem ramSlice240 : (data.ram.drop 240).take 16 = (ramSource.drop 240).take 16 :=
  ramLeaf240.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryFrameNative.BlakeRoundUncached.native.ramFields encodeField 240 16)

numeric_data_binding ramLeaf256 : (data.ram.drop 256).take 16 =
  ((Airbender.Compiler.MemoryFrameNative.BlakeRoundUncached.native.ramFields.drop 256).take 16).map encodeField

theorem ramSlice256 : (data.ram.drop 256).take 16 = (ramSource.drop 256).take 16 :=
  ramLeaf256.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryFrameNative.BlakeRoundUncached.native.ramFields encodeField 256 16)

numeric_data_binding ramLeaf272 : (data.ram.drop 272).take 16 =
  ((Airbender.Compiler.MemoryFrameNative.BlakeRoundUncached.native.ramFields.drop 272).take 16).map encodeField

theorem ramSlice272 : (data.ram.drop 272).take 16 = (ramSource.drop 272).take 16 :=
  ramLeaf272.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryFrameNative.BlakeRoundUncached.native.ramFields encodeField 272 16)

numeric_data_binding ramLeaf288 : (data.ram.drop 288).take 16 =
  ((Airbender.Compiler.MemoryFrameNative.BlakeRoundUncached.native.ramFields.drop 288).take 16).map encodeField

theorem ramSlice288 : (data.ram.drop 288).take 16 = (ramSource.drop 288).take 16 :=
  ramLeaf288.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryFrameNative.BlakeRoundUncached.native.ramFields encodeField 288 16)

numeric_data_binding ramLeaf304 : (data.ram.drop 304).take 16 =
  ((Airbender.Compiler.MemoryFrameNative.BlakeRoundUncached.native.ramFields.drop 304).take 16).map encodeField

theorem ramSlice304 : (data.ram.drop 304).take 16 = (ramSource.drop 304).take 16 :=
  ramLeaf304.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryFrameNative.BlakeRoundUncached.native.ramFields encodeField 304 16)

numeric_data_binding ramLeaf320 : (data.ram.drop 320).take 16 =
  ((Airbender.Compiler.MemoryFrameNative.BlakeRoundUncached.native.ramFields.drop 320).take 16).map encodeField

theorem ramSlice320 : (data.ram.drop 320).take 16 = (ramSource.drop 320).take 16 :=
  ramLeaf320.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryFrameNative.BlakeRoundUncached.native.ramFields encodeField 320 16)

numeric_data_binding ramLeaf336 : (data.ram.drop 336).take 16 =
  ((Airbender.Compiler.MemoryFrameNative.BlakeRoundUncached.native.ramFields.drop 336).take 16).map encodeField

theorem ramSlice336 : (data.ram.drop 336).take 16 = (ramSource.drop 336).take 16 :=
  ramLeaf336.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryFrameNative.BlakeRoundUncached.native.ramFields encodeField 336 16)

numeric_data_binding ramLeaf352 : (data.ram.drop 352).take 16 =
  ((Airbender.Compiler.MemoryFrameNative.BlakeRoundUncached.native.ramFields.drop 352).take 16).map encodeField

theorem ramSlice352 : (data.ram.drop 352).take 16 = (ramSource.drop 352).take 16 :=
  ramLeaf352.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryFrameNative.BlakeRoundUncached.native.ramFields encodeField 352 16)

numeric_data_binding ramLeaf368 : (data.ram.drop 368).take 16 =
  ((Airbender.Compiler.MemoryFrameNative.BlakeRoundUncached.native.ramFields.drop 368).take 16).map encodeField

theorem ramSlice368 : (data.ram.drop 368).take 16 = (ramSource.drop 368).take 16 :=
  ramLeaf368.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryFrameNative.BlakeRoundUncached.native.ramFields encodeField 368 16)

numeric_data_binding ramLeaf384 : (data.ram.drop 384).take 16 =
  ((Airbender.Compiler.MemoryFrameNative.BlakeRoundUncached.native.ramFields.drop 384).take 16).map encodeField

theorem ramSlice384 : (data.ram.drop 384).take 16 = (ramSource.drop 384).take 16 :=
  ramLeaf384.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryFrameNative.BlakeRoundUncached.native.ramFields encodeField 384 16)

numeric_data_binding ramLeaf400 : (data.ram.drop 400).take 16 =
  ((Airbender.Compiler.MemoryFrameNative.BlakeRoundUncached.native.ramFields.drop 400).take 16).map encodeField

theorem ramSlice400 : (data.ram.drop 400).take 16 = (ramSource.drop 400).take 16 :=
  ramLeaf400.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryFrameNative.BlakeRoundUncached.native.ramFields encodeField 400 16)

numeric_data_binding ramLeaf416 : (data.ram.drop 416).take 16 =
  ((Airbender.Compiler.MemoryFrameNative.BlakeRoundUncached.native.ramFields.drop 416).take 16).map encodeField

theorem ramSlice416 : (data.ram.drop 416).take 16 = (ramSource.drop 416).take 16 :=
  ramLeaf416.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryFrameNative.BlakeRoundUncached.native.ramFields encodeField 416 16)

numeric_data_binding ramLeaf432 : (data.ram.drop 432).take 16 =
  ((Airbender.Compiler.MemoryFrameNative.BlakeRoundUncached.native.ramFields.drop 432).take 16).map encodeField

theorem ramSlice432 : (data.ram.drop 432).take 16 = (ramSource.drop 432).take 16 :=
  ramLeaf432.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryFrameNative.BlakeRoundUncached.native.ramFields encodeField 432 16)

numeric_data_binding ramLeaf448 : (data.ram.drop 448).take 16 =
  ((Airbender.Compiler.MemoryFrameNative.BlakeRoundUncached.native.ramFields.drop 448).take 16).map encodeField

theorem ramSlice448 : (data.ram.drop 448).take 16 = (ramSource.drop 448).take 16 :=
  ramLeaf448.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryFrameNative.BlakeRoundUncached.native.ramFields encodeField 448 16)

numeric_data_binding ramLeaf464 : (data.ram.drop 464).take 16 =
  ((Airbender.Compiler.MemoryFrameNative.BlakeRoundUncached.native.ramFields.drop 464).take 16).map encodeField

theorem ramSlice464 : (data.ram.drop 464).take 16 = (ramSource.drop 464).take 16 :=
  ramLeaf464.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryFrameNative.BlakeRoundUncached.native.ramFields encodeField 464 16)

numeric_data_binding ramLeaf480 : (data.ram.drop 480).take 16 =
  ((Airbender.Compiler.MemoryFrameNative.BlakeRoundUncached.native.ramFields.drop 480).take 16).map encodeField

theorem ramSlice480 : (data.ram.drop 480).take 16 = (ramSource.drop 480).take 16 :=
  ramLeaf480.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryFrameNative.BlakeRoundUncached.native.ramFields encodeField 480 16)

numeric_data_binding ramLeaf496 : (data.ram.drop 496).take 16 =
  ((Airbender.Compiler.MemoryFrameNative.BlakeRoundUncached.native.ramFields.drop 496).take 16).map encodeField

theorem ramSlice496 : (data.ram.drop 496).take 16 = (ramSource.drop 496).take 16 :=
  ramLeaf496.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryFrameNative.BlakeRoundUncached.native.ramFields encodeField 496 16)

numeric_data_binding ramLeaf512 : (data.ram.drop 512).take 16 =
  ((Airbender.Compiler.MemoryFrameNative.BlakeRoundUncached.native.ramFields.drop 512).take 16).map encodeField

theorem ramSlice512 : (data.ram.drop 512).take 16 = (ramSource.drop 512).take 16 :=
  ramLeaf512.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryFrameNative.BlakeRoundUncached.native.ramFields encodeField 512 16)

numeric_data_binding ramLeaf528 : (data.ram.drop 528).take 16 =
  ((Airbender.Compiler.MemoryFrameNative.BlakeRoundUncached.native.ramFields.drop 528).take 16).map encodeField

theorem ramSlice528 : (data.ram.drop 528).take 16 = (ramSource.drop 528).take 16 :=
  ramLeaf528.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryFrameNative.BlakeRoundUncached.native.ramFields encodeField 528 16)

numeric_data_binding ramLeaf544 : (data.ram.drop 544).take 16 =
  ((Airbender.Compiler.MemoryFrameNative.BlakeRoundUncached.native.ramFields.drop 544).take 16).map encodeField

theorem ramSlice544 : (data.ram.drop 544).take 16 = (ramSource.drop 544).take 16 :=
  ramLeaf544.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryFrameNative.BlakeRoundUncached.native.ramFields encodeField 544 16)

numeric_data_binding ramLeaf560 : (data.ram.drop 560).take 16 =
  ((Airbender.Compiler.MemoryFrameNative.BlakeRoundUncached.native.ramFields.drop 560).take 16).map encodeField

theorem ramSlice560 : (data.ram.drop 560).take 16 = (ramSource.drop 560).take 16 :=
  ramLeaf560.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryFrameNative.BlakeRoundUncached.native.ramFields encodeField 560 16)

numeric_data_binding ramLeaf576 : (data.ram.drop 576).take 16 =
  ((Airbender.Compiler.MemoryFrameNative.BlakeRoundUncached.native.ramFields.drop 576).take 16).map encodeField

theorem ramSlice576 : (data.ram.drop 576).take 16 = (ramSource.drop 576).take 16 :=
  ramLeaf576.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryFrameNative.BlakeRoundUncached.native.ramFields encodeField 576 16)

numeric_data_binding ramLeaf592 : (data.ram.drop 592).take 16 =
  ((Airbender.Compiler.MemoryFrameNative.BlakeRoundUncached.native.ramFields.drop 592).take 16).map encodeField

theorem ramSlice592 : (data.ram.drop 592).take 16 = (ramSource.drop 592).take 16 :=
  ramLeaf592.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryFrameNative.BlakeRoundUncached.native.ramFields encodeField 592 16)

numeric_data_binding ramLeaf608 : (data.ram.drop 608).take 8 =
  ((Airbender.Compiler.MemoryFrameNative.BlakeRoundUncached.native.ramFields.drop 608).take 8).map encodeField

theorem ramSlice608 : (data.ram.drop 608).take 8 = (ramSource.drop 608).take 8 :=
  ramLeaf608.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryFrameNative.BlakeRoundUncached.native.ramFields encodeField 608 8)

theorem ramNode0_32 : (data.ram.drop 0).take 32 = (ramSource.drop 0).take 32 :=
  NumericQueryFrameChecks.merge_bindings data.ram ramSource 0 16 16 ramSlice0 ramSlice16

theorem ramNode32_32 : (data.ram.drop 32).take 32 = (ramSource.drop 32).take 32 :=
  NumericQueryFrameChecks.merge_bindings data.ram ramSource 32 16 16 ramSlice32 ramSlice48

theorem ramNode0_64 : (data.ram.drop 0).take 64 = (ramSource.drop 0).take 64 :=
  NumericQueryFrameChecks.merge_bindings data.ram ramSource 0 32 32 ramNode0_32 ramNode32_32

theorem ramNode64_32 : (data.ram.drop 64).take 32 = (ramSource.drop 64).take 32 :=
  NumericQueryFrameChecks.merge_bindings data.ram ramSource 64 16 16 ramSlice64 ramSlice80

theorem ramNode112_32 : (data.ram.drop 112).take 32 = (ramSource.drop 112).take 32 :=
  NumericQueryFrameChecks.merge_bindings data.ram ramSource 112 16 16 ramSlice112 ramSlice128

theorem ramNode96_48 : (data.ram.drop 96).take 48 = (ramSource.drop 96).take 48 :=
  NumericQueryFrameChecks.merge_bindings data.ram ramSource 96 16 32 ramSlice96 ramNode112_32

theorem ramNode64_80 : (data.ram.drop 64).take 80 = (ramSource.drop 64).take 80 :=
  NumericQueryFrameChecks.merge_bindings data.ram ramSource 64 32 48 ramNode64_32 ramNode96_48

theorem ramNode0_144 : (data.ram.drop 0).take 144 = (ramSource.drop 0).take 144 :=
  NumericQueryFrameChecks.merge_bindings data.ram ramSource 0 64 80 ramNode0_64 ramNode64_80

theorem ramNode144_32 : (data.ram.drop 144).take 32 = (ramSource.drop 144).take 32 :=
  NumericQueryFrameChecks.merge_bindings data.ram ramSource 144 16 16 ramSlice144 ramSlice160

theorem ramNode192_32 : (data.ram.drop 192).take 32 = (ramSource.drop 192).take 32 :=
  NumericQueryFrameChecks.merge_bindings data.ram ramSource 192 16 16 ramSlice192 ramSlice208

theorem ramNode176_48 : (data.ram.drop 176).take 48 = (ramSource.drop 176).take 48 :=
  NumericQueryFrameChecks.merge_bindings data.ram ramSource 176 16 32 ramSlice176 ramNode192_32

theorem ramNode144_80 : (data.ram.drop 144).take 80 = (ramSource.drop 144).take 80 :=
  NumericQueryFrameChecks.merge_bindings data.ram ramSource 144 32 48 ramNode144_32 ramNode176_48

theorem ramNode224_32 : (data.ram.drop 224).take 32 = (ramSource.drop 224).take 32 :=
  NumericQueryFrameChecks.merge_bindings data.ram ramSource 224 16 16 ramSlice224 ramSlice240

theorem ramNode272_32 : (data.ram.drop 272).take 32 = (ramSource.drop 272).take 32 :=
  NumericQueryFrameChecks.merge_bindings data.ram ramSource 272 16 16 ramSlice272 ramSlice288

theorem ramNode256_48 : (data.ram.drop 256).take 48 = (ramSource.drop 256).take 48 :=
  NumericQueryFrameChecks.merge_bindings data.ram ramSource 256 16 32 ramSlice256 ramNode272_32

theorem ramNode224_80 : (data.ram.drop 224).take 80 = (ramSource.drop 224).take 80 :=
  NumericQueryFrameChecks.merge_bindings data.ram ramSource 224 32 48 ramNode224_32 ramNode256_48

theorem ramNode144_160 : (data.ram.drop 144).take 160 = (ramSource.drop 144).take 160 :=
  NumericQueryFrameChecks.merge_bindings data.ram ramSource 144 80 80 ramNode144_80 ramNode224_80

theorem ramNode0_304 : (data.ram.drop 0).take 304 = (ramSource.drop 0).take 304 :=
  NumericQueryFrameChecks.merge_bindings data.ram ramSource 0 144 160 ramNode0_144 ramNode144_160

theorem ramNode304_32 : (data.ram.drop 304).take 32 = (ramSource.drop 304).take 32 :=
  NumericQueryFrameChecks.merge_bindings data.ram ramSource 304 16 16 ramSlice304 ramSlice320

theorem ramNode352_32 : (data.ram.drop 352).take 32 = (ramSource.drop 352).take 32 :=
  NumericQueryFrameChecks.merge_bindings data.ram ramSource 352 16 16 ramSlice352 ramSlice368

theorem ramNode336_48 : (data.ram.drop 336).take 48 = (ramSource.drop 336).take 48 :=
  NumericQueryFrameChecks.merge_bindings data.ram ramSource 336 16 32 ramSlice336 ramNode352_32

theorem ramNode304_80 : (data.ram.drop 304).take 80 = (ramSource.drop 304).take 80 :=
  NumericQueryFrameChecks.merge_bindings data.ram ramSource 304 32 48 ramNode304_32 ramNode336_48

theorem ramNode384_32 : (data.ram.drop 384).take 32 = (ramSource.drop 384).take 32 :=
  NumericQueryFrameChecks.merge_bindings data.ram ramSource 384 16 16 ramSlice384 ramSlice400

theorem ramNode432_32 : (data.ram.drop 432).take 32 = (ramSource.drop 432).take 32 :=
  NumericQueryFrameChecks.merge_bindings data.ram ramSource 432 16 16 ramSlice432 ramSlice448

theorem ramNode416_48 : (data.ram.drop 416).take 48 = (ramSource.drop 416).take 48 :=
  NumericQueryFrameChecks.merge_bindings data.ram ramSource 416 16 32 ramSlice416 ramNode432_32

theorem ramNode384_80 : (data.ram.drop 384).take 80 = (ramSource.drop 384).take 80 :=
  NumericQueryFrameChecks.merge_bindings data.ram ramSource 384 32 48 ramNode384_32 ramNode416_48

theorem ramNode304_160 : (data.ram.drop 304).take 160 = (ramSource.drop 304).take 160 :=
  NumericQueryFrameChecks.merge_bindings data.ram ramSource 304 80 80 ramNode304_80 ramNode384_80

theorem ramNode464_32 : (data.ram.drop 464).take 32 = (ramSource.drop 464).take 32 :=
  NumericQueryFrameChecks.merge_bindings data.ram ramSource 464 16 16 ramSlice464 ramSlice480

theorem ramNode512_32 : (data.ram.drop 512).take 32 = (ramSource.drop 512).take 32 :=
  NumericQueryFrameChecks.merge_bindings data.ram ramSource 512 16 16 ramSlice512 ramSlice528

theorem ramNode496_48 : (data.ram.drop 496).take 48 = (ramSource.drop 496).take 48 :=
  NumericQueryFrameChecks.merge_bindings data.ram ramSource 496 16 32 ramSlice496 ramNode512_32

theorem ramNode464_80 : (data.ram.drop 464).take 80 = (ramSource.drop 464).take 80 :=
  NumericQueryFrameChecks.merge_bindings data.ram ramSource 464 32 48 ramNode464_32 ramNode496_48

theorem ramNode544_32 : (data.ram.drop 544).take 32 = (ramSource.drop 544).take 32 :=
  NumericQueryFrameChecks.merge_bindings data.ram ramSource 544 16 16 ramSlice544 ramSlice560

theorem ramNode592_24 : (data.ram.drop 592).take 24 = (ramSource.drop 592).take 24 :=
  NumericQueryFrameChecks.merge_bindings data.ram ramSource 592 16 8 ramSlice592 ramSlice608

theorem ramNode576_40 : (data.ram.drop 576).take 40 = (ramSource.drop 576).take 40 :=
  NumericQueryFrameChecks.merge_bindings data.ram ramSource 576 16 24 ramSlice576 ramNode592_24

theorem ramNode544_72 : (data.ram.drop 544).take 72 = (ramSource.drop 544).take 72 :=
  NumericQueryFrameChecks.merge_bindings data.ram ramSource 544 32 40 ramNode544_32 ramNode576_40

theorem ramNode464_152 : (data.ram.drop 464).take 152 = (ramSource.drop 464).take 152 :=
  NumericQueryFrameChecks.merge_bindings data.ram ramSource 464 80 72 ramNode464_80 ramNode544_72

theorem ramNode304_312 : (data.ram.drop 304).take 312 = (ramSource.drop 304).take 312 :=
  NumericQueryFrameChecks.merge_bindings data.ram ramSource 304 160 152 ramNode304_160 ramNode464_152

theorem ramNode0_616 : (data.ram.drop 0).take 616 = (ramSource.drop 0).take 616 :=
  NumericQueryFrameChecks.merge_bindings data.ram ramSource 0 304 312 ramNode0_304 ramNode304_312

theorem ramLength : Airbender.Compiler.MemoryFrameNative.BlakeRoundUncached.native.ramFields.length = 616 := by decide +kernel

theorem ram_binding : data.ram = ramSource :=
  NumericQueryFrameChecks.complete_binding data.ram ramSource 616
    (by decide +kernel) (by rw [ramSource, List.length_map, ramLength]) ramNode0_616

numeric_data_binding initialization_binding : data.initialization = Airbender.Compiler.MemoryFrameNative.BlakeRoundUncached.native.initializationFields.map encodeField

numeric_data_binding execution_binding : data.execution = Airbender.Compiler.MemoryFrameNative.BlakeRoundUncached.native.executeFields.map encodeField

end Airbender.Compiler.MemoryFrameChecks.BlakeRoundUncached
