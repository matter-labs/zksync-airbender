import Airbender.Proofs.GKRProtocol.QueryFrameChecks.BlakeRoundCached.Data
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.QueryFrameChecks.BlakeRoundCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def encodeField : Source.EncodedField → NumericPolynomialChecks.Data × NumericPolynomialChecks.Data := (fun field : Source.EncodedField => (NumericPolynomialChecks.encode (field.polynomial Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.originalProjection), NumericPolynomialChecks.encode (field.polynomial Airbender.Compiler.LookupNative.BlakeRoundCached.native.sourcePlacement)))

noncomputable def fieldsSource := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields.map encodeField

numeric_data_binding fieldsLeaf0 : (data.fields.drop 0).take 16 =
  ((Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields.drop 0).take 16).map encodeField

theorem fieldsSlice0 : (data.fields.drop 0).take 16 = (fieldsSource.drop 0).take 16 :=
  fieldsLeaf0.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields encodeField 0 16)

numeric_data_binding fieldsLeaf16 : (data.fields.drop 16).take 16 =
  ((Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields.drop 16).take 16).map encodeField

theorem fieldsSlice16 : (data.fields.drop 16).take 16 = (fieldsSource.drop 16).take 16 :=
  fieldsLeaf16.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields encodeField 16 16)

numeric_data_binding fieldsLeaf32 : (data.fields.drop 32).take 16 =
  ((Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields.drop 32).take 16).map encodeField

theorem fieldsSlice32 : (data.fields.drop 32).take 16 = (fieldsSource.drop 32).take 16 :=
  fieldsLeaf32.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields encodeField 32 16)

numeric_data_binding fieldsLeaf48 : (data.fields.drop 48).take 16 =
  ((Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields.drop 48).take 16).map encodeField

theorem fieldsSlice48 : (data.fields.drop 48).take 16 = (fieldsSource.drop 48).take 16 :=
  fieldsLeaf48.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields encodeField 48 16)

numeric_data_binding fieldsLeaf64 : (data.fields.drop 64).take 16 =
  ((Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields.drop 64).take 16).map encodeField

theorem fieldsSlice64 : (data.fields.drop 64).take 16 = (fieldsSource.drop 64).take 16 :=
  fieldsLeaf64.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields encodeField 64 16)

numeric_data_binding fieldsLeaf80 : (data.fields.drop 80).take 16 =
  ((Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields.drop 80).take 16).map encodeField

theorem fieldsSlice80 : (data.fields.drop 80).take 16 = (fieldsSource.drop 80).take 16 :=
  fieldsLeaf80.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields encodeField 80 16)

numeric_data_binding fieldsLeaf96 : (data.fields.drop 96).take 16 =
  ((Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields.drop 96).take 16).map encodeField

theorem fieldsSlice96 : (data.fields.drop 96).take 16 = (fieldsSource.drop 96).take 16 :=
  fieldsLeaf96.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields encodeField 96 16)

numeric_data_binding fieldsLeaf112 : (data.fields.drop 112).take 16 =
  ((Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields.drop 112).take 16).map encodeField

theorem fieldsSlice112 : (data.fields.drop 112).take 16 = (fieldsSource.drop 112).take 16 :=
  fieldsLeaf112.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields encodeField 112 16)

numeric_data_binding fieldsLeaf128 : (data.fields.drop 128).take 16 =
  ((Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields.drop 128).take 16).map encodeField

theorem fieldsSlice128 : (data.fields.drop 128).take 16 = (fieldsSource.drop 128).take 16 :=
  fieldsLeaf128.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields encodeField 128 16)

numeric_data_binding fieldsLeaf144 : (data.fields.drop 144).take 16 =
  ((Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields.drop 144).take 16).map encodeField

theorem fieldsSlice144 : (data.fields.drop 144).take 16 = (fieldsSource.drop 144).take 16 :=
  fieldsLeaf144.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields encodeField 144 16)

numeric_data_binding fieldsLeaf160 : (data.fields.drop 160).take 16 =
  ((Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields.drop 160).take 16).map encodeField

theorem fieldsSlice160 : (data.fields.drop 160).take 16 = (fieldsSource.drop 160).take 16 :=
  fieldsLeaf160.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields encodeField 160 16)

numeric_data_binding fieldsLeaf176 : (data.fields.drop 176).take 16 =
  ((Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields.drop 176).take 16).map encodeField

theorem fieldsSlice176 : (data.fields.drop 176).take 16 = (fieldsSource.drop 176).take 16 :=
  fieldsLeaf176.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields encodeField 176 16)

numeric_data_binding fieldsLeaf192 : (data.fields.drop 192).take 16 =
  ((Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields.drop 192).take 16).map encodeField

theorem fieldsSlice192 : (data.fields.drop 192).take 16 = (fieldsSource.drop 192).take 16 :=
  fieldsLeaf192.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields encodeField 192 16)

numeric_data_binding fieldsLeaf208 : (data.fields.drop 208).take 16 =
  ((Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields.drop 208).take 16).map encodeField

theorem fieldsSlice208 : (data.fields.drop 208).take 16 = (fieldsSource.drop 208).take 16 :=
  fieldsLeaf208.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields encodeField 208 16)

numeric_data_binding fieldsLeaf224 : (data.fields.drop 224).take 16 =
  ((Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields.drop 224).take 16).map encodeField

theorem fieldsSlice224 : (data.fields.drop 224).take 16 = (fieldsSource.drop 224).take 16 :=
  fieldsLeaf224.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields encodeField 224 16)

numeric_data_binding fieldsLeaf240 : (data.fields.drop 240).take 16 =
  ((Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields.drop 240).take 16).map encodeField

theorem fieldsSlice240 : (data.fields.drop 240).take 16 = (fieldsSource.drop 240).take 16 :=
  fieldsLeaf240.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields encodeField 240 16)

numeric_data_binding fieldsLeaf256 : (data.fields.drop 256).take 16 =
  ((Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields.drop 256).take 16).map encodeField

theorem fieldsSlice256 : (data.fields.drop 256).take 16 = (fieldsSource.drop 256).take 16 :=
  fieldsLeaf256.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields encodeField 256 16)

numeric_data_binding fieldsLeaf272 : (data.fields.drop 272).take 16 =
  ((Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields.drop 272).take 16).map encodeField

theorem fieldsSlice272 : (data.fields.drop 272).take 16 = (fieldsSource.drop 272).take 16 :=
  fieldsLeaf272.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields encodeField 272 16)

numeric_data_binding fieldsLeaf288 : (data.fields.drop 288).take 16 =
  ((Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields.drop 288).take 16).map encodeField

theorem fieldsSlice288 : (data.fields.drop 288).take 16 = (fieldsSource.drop 288).take 16 :=
  fieldsLeaf288.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields encodeField 288 16)

numeric_data_binding fieldsLeaf304 : (data.fields.drop 304).take 16 =
  ((Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields.drop 304).take 16).map encodeField

theorem fieldsSlice304 : (data.fields.drop 304).take 16 = (fieldsSource.drop 304).take 16 :=
  fieldsLeaf304.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields encodeField 304 16)

numeric_data_binding fieldsLeaf320 : (data.fields.drop 320).take 16 =
  ((Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields.drop 320).take 16).map encodeField

theorem fieldsSlice320 : (data.fields.drop 320).take 16 = (fieldsSource.drop 320).take 16 :=
  fieldsLeaf320.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields encodeField 320 16)

numeric_data_binding fieldsLeaf336 : (data.fields.drop 336).take 16 =
  ((Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields.drop 336).take 16).map encodeField

theorem fieldsSlice336 : (data.fields.drop 336).take 16 = (fieldsSource.drop 336).take 16 :=
  fieldsLeaf336.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields encodeField 336 16)

numeric_data_binding fieldsLeaf352 : (data.fields.drop 352).take 16 =
  ((Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields.drop 352).take 16).map encodeField

theorem fieldsSlice352 : (data.fields.drop 352).take 16 = (fieldsSource.drop 352).take 16 :=
  fieldsLeaf352.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields encodeField 352 16)

numeric_data_binding fieldsLeaf368 : (data.fields.drop 368).take 16 =
  ((Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields.drop 368).take 16).map encodeField

theorem fieldsSlice368 : (data.fields.drop 368).take 16 = (fieldsSource.drop 368).take 16 :=
  fieldsLeaf368.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields encodeField 368 16)

numeric_data_binding fieldsLeaf384 : (data.fields.drop 384).take 16 =
  ((Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields.drop 384).take 16).map encodeField

theorem fieldsSlice384 : (data.fields.drop 384).take 16 = (fieldsSource.drop 384).take 16 :=
  fieldsLeaf384.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields encodeField 384 16)

numeric_data_binding fieldsLeaf400 : (data.fields.drop 400).take 16 =
  ((Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields.drop 400).take 16).map encodeField

theorem fieldsSlice400 : (data.fields.drop 400).take 16 = (fieldsSource.drop 400).take 16 :=
  fieldsLeaf400.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields encodeField 400 16)

numeric_data_binding fieldsLeaf416 : (data.fields.drop 416).take 16 =
  ((Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields.drop 416).take 16).map encodeField

theorem fieldsSlice416 : (data.fields.drop 416).take 16 = (fieldsSource.drop 416).take 16 :=
  fieldsLeaf416.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields encodeField 416 16)

numeric_data_binding fieldsLeaf432 : (data.fields.drop 432).take 16 =
  ((Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields.drop 432).take 16).map encodeField

theorem fieldsSlice432 : (data.fields.drop 432).take 16 = (fieldsSource.drop 432).take 16 :=
  fieldsLeaf432.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields encodeField 432 16)

numeric_data_binding fieldsLeaf448 : (data.fields.drop 448).take 16 =
  ((Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields.drop 448).take 16).map encodeField

theorem fieldsSlice448 : (data.fields.drop 448).take 16 = (fieldsSource.drop 448).take 16 :=
  fieldsLeaf448.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields encodeField 448 16)

numeric_data_binding fieldsLeaf464 : (data.fields.drop 464).take 16 =
  ((Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields.drop 464).take 16).map encodeField

theorem fieldsSlice464 : (data.fields.drop 464).take 16 = (fieldsSource.drop 464).take 16 :=
  fieldsLeaf464.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields encodeField 464 16)

numeric_data_binding fieldsLeaf480 : (data.fields.drop 480).take 16 =
  ((Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields.drop 480).take 16).map encodeField

theorem fieldsSlice480 : (data.fields.drop 480).take 16 = (fieldsSource.drop 480).take 16 :=
  fieldsLeaf480.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields encodeField 480 16)

numeric_data_binding fieldsLeaf496 : (data.fields.drop 496).take 16 =
  ((Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields.drop 496).take 16).map encodeField

theorem fieldsSlice496 : (data.fields.drop 496).take 16 = (fieldsSource.drop 496).take 16 :=
  fieldsLeaf496.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields encodeField 496 16)

numeric_data_binding fieldsLeaf512 : (data.fields.drop 512).take 16 =
  ((Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields.drop 512).take 16).map encodeField

theorem fieldsSlice512 : (data.fields.drop 512).take 16 = (fieldsSource.drop 512).take 16 :=
  fieldsLeaf512.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields encodeField 512 16)

numeric_data_binding fieldsLeaf528 : (data.fields.drop 528).take 16 =
  ((Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields.drop 528).take 16).map encodeField

theorem fieldsSlice528 : (data.fields.drop 528).take 16 = (fieldsSource.drop 528).take 16 :=
  fieldsLeaf528.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields encodeField 528 16)

numeric_data_binding fieldsLeaf544 : (data.fields.drop 544).take 16 =
  ((Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields.drop 544).take 16).map encodeField

theorem fieldsSlice544 : (data.fields.drop 544).take 16 = (fieldsSource.drop 544).take 16 :=
  fieldsLeaf544.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields encodeField 544 16)

numeric_data_binding fieldsLeaf560 : (data.fields.drop 560).take 16 =
  ((Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields.drop 560).take 16).map encodeField

theorem fieldsSlice560 : (data.fields.drop 560).take 16 = (fieldsSource.drop 560).take 16 :=
  fieldsLeaf560.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields encodeField 560 16)

numeric_data_binding fieldsLeaf576 : (data.fields.drop 576).take 16 =
  ((Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields.drop 576).take 16).map encodeField

theorem fieldsSlice576 : (data.fields.drop 576).take 16 = (fieldsSource.drop 576).take 16 :=
  fieldsLeaf576.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields encodeField 576 16)

numeric_data_binding fieldsLeaf592 : (data.fields.drop 592).take 16 =
  ((Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields.drop 592).take 16).map encodeField

theorem fieldsSlice592 : (data.fields.drop 592).take 16 = (fieldsSource.drop 592).take 16 :=
  fieldsLeaf592.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields encodeField 592 16)

numeric_data_binding fieldsLeaf608 : (data.fields.drop 608).take 16 =
  ((Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields.drop 608).take 16).map encodeField

theorem fieldsSlice608 : (data.fields.drop 608).take 16 = (fieldsSource.drop 608).take 16 :=
  fieldsLeaf608.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields encodeField 608 16)

numeric_data_binding fieldsLeaf624 : (data.fields.drop 624).take 16 =
  ((Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields.drop 624).take 16).map encodeField

theorem fieldsSlice624 : (data.fields.drop 624).take 16 = (fieldsSource.drop 624).take 16 :=
  fieldsLeaf624.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields encodeField 624 16)

numeric_data_binding fieldsLeaf640 : (data.fields.drop 640).take 16 =
  ((Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields.drop 640).take 16).map encodeField

theorem fieldsSlice640 : (data.fields.drop 640).take 16 = (fieldsSource.drop 640).take 16 :=
  fieldsLeaf640.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields encodeField 640 16)

numeric_data_binding fieldsLeaf656 : (data.fields.drop 656).take 16 =
  ((Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields.drop 656).take 16).map encodeField

theorem fieldsSlice656 : (data.fields.drop 656).take 16 = (fieldsSource.drop 656).take 16 :=
  fieldsLeaf656.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields encodeField 656 16)

numeric_data_binding fieldsLeaf672 : (data.fields.drop 672).take 16 =
  ((Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields.drop 672).take 16).map encodeField

theorem fieldsSlice672 : (data.fields.drop 672).take 16 = (fieldsSource.drop 672).take 16 :=
  fieldsLeaf672.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields encodeField 672 16)

numeric_data_binding fieldsLeaf688 : (data.fields.drop 688).take 16 =
  ((Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields.drop 688).take 16).map encodeField

theorem fieldsSlice688 : (data.fields.drop 688).take 16 = (fieldsSource.drop 688).take 16 :=
  fieldsLeaf688.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields encodeField 688 16)

numeric_data_binding fieldsLeaf704 : (data.fields.drop 704).take 16 =
  ((Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields.drop 704).take 16).map encodeField

theorem fieldsSlice704 : (data.fields.drop 704).take 16 = (fieldsSource.drop 704).take 16 :=
  fieldsLeaf704.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields encodeField 704 16)

numeric_data_binding fieldsLeaf720 : (data.fields.drop 720).take 16 =
  ((Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields.drop 720).take 16).map encodeField

theorem fieldsSlice720 : (data.fields.drop 720).take 16 = (fieldsSource.drop 720).take 16 :=
  fieldsLeaf720.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields encodeField 720 16)

numeric_data_binding fieldsLeaf736 : (data.fields.drop 736).take 16 =
  ((Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields.drop 736).take 16).map encodeField

theorem fieldsSlice736 : (data.fields.drop 736).take 16 = (fieldsSource.drop 736).take 16 :=
  fieldsLeaf736.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields encodeField 736 16)

numeric_data_binding fieldsLeaf752 : (data.fields.drop 752).take 16 =
  ((Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields.drop 752).take 16).map encodeField

theorem fieldsSlice752 : (data.fields.drop 752).take 16 = (fieldsSource.drop 752).take 16 :=
  fieldsLeaf752.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields encodeField 752 16)

numeric_data_binding fieldsLeaf768 : (data.fields.drop 768).take 16 =
  ((Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields.drop 768).take 16).map encodeField

theorem fieldsSlice768 : (data.fields.drop 768).take 16 = (fieldsSource.drop 768).take 16 :=
  fieldsLeaf768.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields encodeField 768 16)

numeric_data_binding fieldsLeaf784 : (data.fields.drop 784).take 16 =
  ((Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields.drop 784).take 16).map encodeField

theorem fieldsSlice784 : (data.fields.drop 784).take 16 = (fieldsSource.drop 784).take 16 :=
  fieldsLeaf784.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields encodeField 784 16)

numeric_data_binding fieldsLeaf800 : (data.fields.drop 800).take 16 =
  ((Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields.drop 800).take 16).map encodeField

theorem fieldsSlice800 : (data.fields.drop 800).take 16 = (fieldsSource.drop 800).take 16 :=
  fieldsLeaf800.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields encodeField 800 16)

numeric_data_binding fieldsLeaf816 : (data.fields.drop 816).take 16 =
  ((Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields.drop 816).take 16).map encodeField

theorem fieldsSlice816 : (data.fields.drop 816).take 16 = (fieldsSource.drop 816).take 16 :=
  fieldsLeaf816.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields encodeField 816 16)

numeric_data_binding fieldsLeaf832 : (data.fields.drop 832).take 16 =
  ((Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields.drop 832).take 16).map encodeField

theorem fieldsSlice832 : (data.fields.drop 832).take 16 = (fieldsSource.drop 832).take 16 :=
  fieldsLeaf832.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields encodeField 832 16)

numeric_data_binding fieldsLeaf848 : (data.fields.drop 848).take 16 =
  ((Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields.drop 848).take 16).map encodeField

theorem fieldsSlice848 : (data.fields.drop 848).take 16 = (fieldsSource.drop 848).take 16 :=
  fieldsLeaf848.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields encodeField 848 16)

numeric_data_binding fieldsLeaf864 : (data.fields.drop 864).take 16 =
  ((Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields.drop 864).take 16).map encodeField

theorem fieldsSlice864 : (data.fields.drop 864).take 16 = (fieldsSource.drop 864).take 16 :=
  fieldsLeaf864.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields encodeField 864 16)

numeric_data_binding fieldsLeaf880 : (data.fields.drop 880).take 16 =
  ((Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields.drop 880).take 16).map encodeField

theorem fieldsSlice880 : (data.fields.drop 880).take 16 = (fieldsSource.drop 880).take 16 :=
  fieldsLeaf880.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields encodeField 880 16)

numeric_data_binding fieldsLeaf896 : (data.fields.drop 896).take 16 =
  ((Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields.drop 896).take 16).map encodeField

theorem fieldsSlice896 : (data.fields.drop 896).take 16 = (fieldsSource.drop 896).take 16 :=
  fieldsLeaf896.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields encodeField 896 16)

numeric_data_binding fieldsLeaf912 : (data.fields.drop 912).take 16 =
  ((Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields.drop 912).take 16).map encodeField

theorem fieldsSlice912 : (data.fields.drop 912).take 16 = (fieldsSource.drop 912).take 16 :=
  fieldsLeaf912.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields encodeField 912 16)

numeric_data_binding fieldsLeaf928 : (data.fields.drop 928).take 16 =
  ((Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields.drop 928).take 16).map encodeField

theorem fieldsSlice928 : (data.fields.drop 928).take 16 = (fieldsSource.drop 928).take 16 :=
  fieldsLeaf928.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields encodeField 928 16)

numeric_data_binding fieldsLeaf944 : (data.fields.drop 944).take 16 =
  ((Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields.drop 944).take 16).map encodeField

theorem fieldsSlice944 : (data.fields.drop 944).take 16 = (fieldsSource.drop 944).take 16 :=
  fieldsLeaf944.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields encodeField 944 16)

numeric_data_binding fieldsLeaf960 : (data.fields.drop 960).take 16 =
  ((Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields.drop 960).take 16).map encodeField

theorem fieldsSlice960 : (data.fields.drop 960).take 16 = (fieldsSource.drop 960).take 16 :=
  fieldsLeaf960.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields encodeField 960 16)

numeric_data_binding fieldsLeaf976 : (data.fields.drop 976).take 16 =
  ((Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields.drop 976).take 16).map encodeField

theorem fieldsSlice976 : (data.fields.drop 976).take 16 = (fieldsSource.drop 976).take 16 :=
  fieldsLeaf976.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields encodeField 976 16)

numeric_data_binding fieldsLeaf992 : (data.fields.drop 992).take 16 =
  ((Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields.drop 992).take 16).map encodeField

theorem fieldsSlice992 : (data.fields.drop 992).take 16 = (fieldsSource.drop 992).take 16 :=
  fieldsLeaf992.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields encodeField 992 16)

numeric_data_binding fieldsLeaf1008 : (data.fields.drop 1008).take 16 =
  ((Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields.drop 1008).take 16).map encodeField

theorem fieldsSlice1008 : (data.fields.drop 1008).take 16 = (fieldsSource.drop 1008).take 16 :=
  fieldsLeaf1008.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields encodeField 1008 16)

numeric_data_binding fieldsLeaf1024 : (data.fields.drop 1024).take 16 =
  ((Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields.drop 1024).take 16).map encodeField

theorem fieldsSlice1024 : (data.fields.drop 1024).take 16 = (fieldsSource.drop 1024).take 16 :=
  fieldsLeaf1024.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields encodeField 1024 16)

numeric_data_binding fieldsLeaf1040 : (data.fields.drop 1040).take 16 =
  ((Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields.drop 1040).take 16).map encodeField

theorem fieldsSlice1040 : (data.fields.drop 1040).take 16 = (fieldsSource.drop 1040).take 16 :=
  fieldsLeaf1040.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields encodeField 1040 16)

numeric_data_binding fieldsLeaf1056 : (data.fields.drop 1056).take 16 =
  ((Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields.drop 1056).take 16).map encodeField

theorem fieldsSlice1056 : (data.fields.drop 1056).take 16 = (fieldsSource.drop 1056).take 16 :=
  fieldsLeaf1056.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields encodeField 1056 16)

numeric_data_binding fieldsLeaf1072 : (data.fields.drop 1072).take 16 =
  ((Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields.drop 1072).take 16).map encodeField

theorem fieldsSlice1072 : (data.fields.drop 1072).take 16 = (fieldsSource.drop 1072).take 16 :=
  fieldsLeaf1072.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields encodeField 1072 16)

numeric_data_binding fieldsLeaf1088 : (data.fields.drop 1088).take 16 =
  ((Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields.drop 1088).take 16).map encodeField

theorem fieldsSlice1088 : (data.fields.drop 1088).take 16 = (fieldsSource.drop 1088).take 16 :=
  fieldsLeaf1088.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields encodeField 1088 16)

numeric_data_binding fieldsLeaf1104 : (data.fields.drop 1104).take 16 =
  ((Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields.drop 1104).take 16).map encodeField

theorem fieldsSlice1104 : (data.fields.drop 1104).take 16 = (fieldsSource.drop 1104).take 16 :=
  fieldsLeaf1104.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields encodeField 1104 16)

numeric_data_binding fieldsLeaf1120 : (data.fields.drop 1120).take 16 =
  ((Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields.drop 1120).take 16).map encodeField

theorem fieldsSlice1120 : (data.fields.drop 1120).take 16 = (fieldsSource.drop 1120).take 16 :=
  fieldsLeaf1120.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields encodeField 1120 16)

numeric_data_binding fieldsLeaf1136 : (data.fields.drop 1136).take 16 =
  ((Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields.drop 1136).take 16).map encodeField

theorem fieldsSlice1136 : (data.fields.drop 1136).take 16 = (fieldsSource.drop 1136).take 16 :=
  fieldsLeaf1136.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields encodeField 1136 16)

theorem fieldsNode0_32 : (data.fields.drop 0).take 32 = (fieldsSource.drop 0).take 32 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 0 16 16 fieldsSlice0 fieldsSlice16

theorem fieldsNode32_32 : (data.fields.drop 32).take 32 = (fieldsSource.drop 32).take 32 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 32 16 16 fieldsSlice32 fieldsSlice48

theorem fieldsNode0_64 : (data.fields.drop 0).take 64 = (fieldsSource.drop 0).take 64 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 0 32 32 fieldsNode0_32 fieldsNode32_32

theorem fieldsNode64_32 : (data.fields.drop 64).take 32 = (fieldsSource.drop 64).take 32 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 64 16 16 fieldsSlice64 fieldsSlice80

theorem fieldsNode112_32 : (data.fields.drop 112).take 32 = (fieldsSource.drop 112).take 32 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 112 16 16 fieldsSlice112 fieldsSlice128

theorem fieldsNode96_48 : (data.fields.drop 96).take 48 = (fieldsSource.drop 96).take 48 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 96 16 32 fieldsSlice96 fieldsNode112_32

theorem fieldsNode64_80 : (data.fields.drop 64).take 80 = (fieldsSource.drop 64).take 80 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 64 32 48 fieldsNode64_32 fieldsNode96_48

theorem fieldsNode0_144 : (data.fields.drop 0).take 144 = (fieldsSource.drop 0).take 144 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 0 64 80 fieldsNode0_64 fieldsNode64_80

theorem fieldsNode144_32 : (data.fields.drop 144).take 32 = (fieldsSource.drop 144).take 32 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 144 16 16 fieldsSlice144 fieldsSlice160

theorem fieldsNode176_32 : (data.fields.drop 176).take 32 = (fieldsSource.drop 176).take 32 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 176 16 16 fieldsSlice176 fieldsSlice192

theorem fieldsNode144_64 : (data.fields.drop 144).take 64 = (fieldsSource.drop 144).take 64 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 144 32 32 fieldsNode144_32 fieldsNode176_32

theorem fieldsNode208_32 : (data.fields.drop 208).take 32 = (fieldsSource.drop 208).take 32 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 208 16 16 fieldsSlice208 fieldsSlice224

theorem fieldsNode256_32 : (data.fields.drop 256).take 32 = (fieldsSource.drop 256).take 32 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 256 16 16 fieldsSlice256 fieldsSlice272

theorem fieldsNode240_48 : (data.fields.drop 240).take 48 = (fieldsSource.drop 240).take 48 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 240 16 32 fieldsSlice240 fieldsNode256_32

theorem fieldsNode208_80 : (data.fields.drop 208).take 80 = (fieldsSource.drop 208).take 80 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 208 32 48 fieldsNode208_32 fieldsNode240_48

theorem fieldsNode144_144 : (data.fields.drop 144).take 144 = (fieldsSource.drop 144).take 144 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 144 64 80 fieldsNode144_64 fieldsNode208_80

theorem fieldsNode0_288 : (data.fields.drop 0).take 288 = (fieldsSource.drop 0).take 288 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 0 144 144 fieldsNode0_144 fieldsNode144_144

theorem fieldsNode288_32 : (data.fields.drop 288).take 32 = (fieldsSource.drop 288).take 32 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 288 16 16 fieldsSlice288 fieldsSlice304

theorem fieldsNode320_32 : (data.fields.drop 320).take 32 = (fieldsSource.drop 320).take 32 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 320 16 16 fieldsSlice320 fieldsSlice336

theorem fieldsNode288_64 : (data.fields.drop 288).take 64 = (fieldsSource.drop 288).take 64 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 288 32 32 fieldsNode288_32 fieldsNode320_32

theorem fieldsNode352_32 : (data.fields.drop 352).take 32 = (fieldsSource.drop 352).take 32 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 352 16 16 fieldsSlice352 fieldsSlice368

theorem fieldsNode400_32 : (data.fields.drop 400).take 32 = (fieldsSource.drop 400).take 32 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 400 16 16 fieldsSlice400 fieldsSlice416

theorem fieldsNode384_48 : (data.fields.drop 384).take 48 = (fieldsSource.drop 384).take 48 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 384 16 32 fieldsSlice384 fieldsNode400_32

theorem fieldsNode352_80 : (data.fields.drop 352).take 80 = (fieldsSource.drop 352).take 80 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 352 32 48 fieldsNode352_32 fieldsNode384_48

theorem fieldsNode288_144 : (data.fields.drop 288).take 144 = (fieldsSource.drop 288).take 144 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 288 64 80 fieldsNode288_64 fieldsNode352_80

theorem fieldsNode432_32 : (data.fields.drop 432).take 32 = (fieldsSource.drop 432).take 32 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 432 16 16 fieldsSlice432 fieldsSlice448

theorem fieldsNode464_32 : (data.fields.drop 464).take 32 = (fieldsSource.drop 464).take 32 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 464 16 16 fieldsSlice464 fieldsSlice480

theorem fieldsNode432_64 : (data.fields.drop 432).take 64 = (fieldsSource.drop 432).take 64 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 432 32 32 fieldsNode432_32 fieldsNode464_32

theorem fieldsNode496_32 : (data.fields.drop 496).take 32 = (fieldsSource.drop 496).take 32 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 496 16 16 fieldsSlice496 fieldsSlice512

theorem fieldsNode544_32 : (data.fields.drop 544).take 32 = (fieldsSource.drop 544).take 32 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 544 16 16 fieldsSlice544 fieldsSlice560

theorem fieldsNode528_48 : (data.fields.drop 528).take 48 = (fieldsSource.drop 528).take 48 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 528 16 32 fieldsSlice528 fieldsNode544_32

theorem fieldsNode496_80 : (data.fields.drop 496).take 80 = (fieldsSource.drop 496).take 80 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 496 32 48 fieldsNode496_32 fieldsNode528_48

theorem fieldsNode432_144 : (data.fields.drop 432).take 144 = (fieldsSource.drop 432).take 144 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 432 64 80 fieldsNode432_64 fieldsNode496_80

theorem fieldsNode288_288 : (data.fields.drop 288).take 288 = (fieldsSource.drop 288).take 288 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 288 144 144 fieldsNode288_144 fieldsNode432_144

theorem fieldsNode0_576 : (data.fields.drop 0).take 576 = (fieldsSource.drop 0).take 576 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 0 288 288 fieldsNode0_288 fieldsNode288_288

theorem fieldsNode576_32 : (data.fields.drop 576).take 32 = (fieldsSource.drop 576).take 32 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 576 16 16 fieldsSlice576 fieldsSlice592

theorem fieldsNode608_32 : (data.fields.drop 608).take 32 = (fieldsSource.drop 608).take 32 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 608 16 16 fieldsSlice608 fieldsSlice624

theorem fieldsNode576_64 : (data.fields.drop 576).take 64 = (fieldsSource.drop 576).take 64 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 576 32 32 fieldsNode576_32 fieldsNode608_32

theorem fieldsNode640_32 : (data.fields.drop 640).take 32 = (fieldsSource.drop 640).take 32 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 640 16 16 fieldsSlice640 fieldsSlice656

theorem fieldsNode688_32 : (data.fields.drop 688).take 32 = (fieldsSource.drop 688).take 32 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 688 16 16 fieldsSlice688 fieldsSlice704

theorem fieldsNode672_48 : (data.fields.drop 672).take 48 = (fieldsSource.drop 672).take 48 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 672 16 32 fieldsSlice672 fieldsNode688_32

theorem fieldsNode640_80 : (data.fields.drop 640).take 80 = (fieldsSource.drop 640).take 80 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 640 32 48 fieldsNode640_32 fieldsNode672_48

theorem fieldsNode576_144 : (data.fields.drop 576).take 144 = (fieldsSource.drop 576).take 144 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 576 64 80 fieldsNode576_64 fieldsNode640_80

theorem fieldsNode720_32 : (data.fields.drop 720).take 32 = (fieldsSource.drop 720).take 32 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 720 16 16 fieldsSlice720 fieldsSlice736

theorem fieldsNode752_32 : (data.fields.drop 752).take 32 = (fieldsSource.drop 752).take 32 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 752 16 16 fieldsSlice752 fieldsSlice768

theorem fieldsNode720_64 : (data.fields.drop 720).take 64 = (fieldsSource.drop 720).take 64 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 720 32 32 fieldsNode720_32 fieldsNode752_32

theorem fieldsNode784_32 : (data.fields.drop 784).take 32 = (fieldsSource.drop 784).take 32 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 784 16 16 fieldsSlice784 fieldsSlice800

theorem fieldsNode832_32 : (data.fields.drop 832).take 32 = (fieldsSource.drop 832).take 32 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 832 16 16 fieldsSlice832 fieldsSlice848

theorem fieldsNode816_48 : (data.fields.drop 816).take 48 = (fieldsSource.drop 816).take 48 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 816 16 32 fieldsSlice816 fieldsNode832_32

theorem fieldsNode784_80 : (data.fields.drop 784).take 80 = (fieldsSource.drop 784).take 80 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 784 32 48 fieldsNode784_32 fieldsNode816_48

theorem fieldsNode720_144 : (data.fields.drop 720).take 144 = (fieldsSource.drop 720).take 144 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 720 64 80 fieldsNode720_64 fieldsNode784_80

theorem fieldsNode576_288 : (data.fields.drop 576).take 288 = (fieldsSource.drop 576).take 288 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 576 144 144 fieldsNode576_144 fieldsNode720_144

theorem fieldsNode864_32 : (data.fields.drop 864).take 32 = (fieldsSource.drop 864).take 32 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 864 16 16 fieldsSlice864 fieldsSlice880

theorem fieldsNode896_32 : (data.fields.drop 896).take 32 = (fieldsSource.drop 896).take 32 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 896 16 16 fieldsSlice896 fieldsSlice912

theorem fieldsNode864_64 : (data.fields.drop 864).take 64 = (fieldsSource.drop 864).take 64 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 864 32 32 fieldsNode864_32 fieldsNode896_32

theorem fieldsNode928_32 : (data.fields.drop 928).take 32 = (fieldsSource.drop 928).take 32 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 928 16 16 fieldsSlice928 fieldsSlice944

theorem fieldsNode976_32 : (data.fields.drop 976).take 32 = (fieldsSource.drop 976).take 32 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 976 16 16 fieldsSlice976 fieldsSlice992

theorem fieldsNode960_48 : (data.fields.drop 960).take 48 = (fieldsSource.drop 960).take 48 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 960 16 32 fieldsSlice960 fieldsNode976_32

theorem fieldsNode928_80 : (data.fields.drop 928).take 80 = (fieldsSource.drop 928).take 80 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 928 32 48 fieldsNode928_32 fieldsNode960_48

theorem fieldsNode864_144 : (data.fields.drop 864).take 144 = (fieldsSource.drop 864).take 144 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 864 64 80 fieldsNode864_64 fieldsNode928_80

theorem fieldsNode1008_32 : (data.fields.drop 1008).take 32 = (fieldsSource.drop 1008).take 32 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 1008 16 16 fieldsSlice1008 fieldsSlice1024

theorem fieldsNode1040_32 : (data.fields.drop 1040).take 32 = (fieldsSource.drop 1040).take 32 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 1040 16 16 fieldsSlice1040 fieldsSlice1056

theorem fieldsNode1008_64 : (data.fields.drop 1008).take 64 = (fieldsSource.drop 1008).take 64 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 1008 32 32 fieldsNode1008_32 fieldsNode1040_32

theorem fieldsNode1072_32 : (data.fields.drop 1072).take 32 = (fieldsSource.drop 1072).take 32 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 1072 16 16 fieldsSlice1072 fieldsSlice1088

theorem fieldsNode1120_32 : (data.fields.drop 1120).take 32 = (fieldsSource.drop 1120).take 32 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 1120 16 16 fieldsSlice1120 fieldsSlice1136

theorem fieldsNode1104_48 : (data.fields.drop 1104).take 48 = (fieldsSource.drop 1104).take 48 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 1104 16 32 fieldsSlice1104 fieldsNode1120_32

theorem fieldsNode1072_80 : (data.fields.drop 1072).take 80 = (fieldsSource.drop 1072).take 80 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 1072 32 48 fieldsNode1072_32 fieldsNode1104_48

theorem fieldsNode1008_144 : (data.fields.drop 1008).take 144 = (fieldsSource.drop 1008).take 144 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 1008 64 80 fieldsNode1008_64 fieldsNode1072_80

theorem fieldsNode864_288 : (data.fields.drop 864).take 288 = (fieldsSource.drop 864).take 288 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 864 144 144 fieldsNode864_144 fieldsNode1008_144

theorem fieldsNode576_576 : (data.fields.drop 576).take 576 = (fieldsSource.drop 576).take 576 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 576 288 288 fieldsNode576_288 fieldsNode864_288

theorem fieldsNode0_1152 : (data.fields.drop 0).take 1152 = (fieldsSource.drop 0).take 1152 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 0 576 576 fieldsNode0_576 fieldsNode576_576

theorem originalFieldsLength : Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields.length = 1152 := by decide +kernel

theorem fields_binding : data.fields = fieldsSource :=
  NumericQueryFrameChecks.complete_binding data.fields fieldsSource 1152
    (by decide +kernel) (by rw [fieldsSource, List.length_map, originalFieldsLength]) fieldsNode0_1152

end Airbender.Compiler.QueryFrameChecks.BlakeRoundCached
