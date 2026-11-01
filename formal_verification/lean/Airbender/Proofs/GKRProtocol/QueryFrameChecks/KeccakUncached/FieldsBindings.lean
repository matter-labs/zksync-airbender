import Airbender.Proofs.GKRProtocol.QueryFrameChecks.KeccakUncached.Data
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.QueryFrameChecks.KeccakUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def encodeField : Source.EncodedField → NumericPolynomialChecks.Data × NumericPolynomialChecks.Data := (fun field : Source.EncodedField => (NumericPolynomialChecks.encode (field.polynomial Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.originalProjection), NumericPolynomialChecks.encode (field.polynomial Airbender.Compiler.LookupNative.KeccakUncached.native.sourcePlacement)))

noncomputable def fieldsSource := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields.map encodeField

numeric_data_binding fieldsLeaf0 : (data.fields.drop 0).take 16 =
  ((Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields.drop 0).take 16).map encodeField

theorem fieldsSlice0 : (data.fields.drop 0).take 16 = (fieldsSource.drop 0).take 16 :=
  fieldsLeaf0.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields encodeField 0 16)

numeric_data_binding fieldsLeaf16 : (data.fields.drop 16).take 16 =
  ((Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields.drop 16).take 16).map encodeField

theorem fieldsSlice16 : (data.fields.drop 16).take 16 = (fieldsSource.drop 16).take 16 :=
  fieldsLeaf16.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields encodeField 16 16)

numeric_data_binding fieldsLeaf32 : (data.fields.drop 32).take 16 =
  ((Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields.drop 32).take 16).map encodeField

theorem fieldsSlice32 : (data.fields.drop 32).take 16 = (fieldsSource.drop 32).take 16 :=
  fieldsLeaf32.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields encodeField 32 16)

numeric_data_binding fieldsLeaf48 : (data.fields.drop 48).take 16 =
  ((Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields.drop 48).take 16).map encodeField

theorem fieldsSlice48 : (data.fields.drop 48).take 16 = (fieldsSource.drop 48).take 16 :=
  fieldsLeaf48.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields encodeField 48 16)

numeric_data_binding fieldsLeaf64 : (data.fields.drop 64).take 16 =
  ((Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields.drop 64).take 16).map encodeField

theorem fieldsSlice64 : (data.fields.drop 64).take 16 = (fieldsSource.drop 64).take 16 :=
  fieldsLeaf64.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields encodeField 64 16)

numeric_data_binding fieldsLeaf80 : (data.fields.drop 80).take 16 =
  ((Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields.drop 80).take 16).map encodeField

theorem fieldsSlice80 : (data.fields.drop 80).take 16 = (fieldsSource.drop 80).take 16 :=
  fieldsLeaf80.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields encodeField 80 16)

numeric_data_binding fieldsLeaf96 : (data.fields.drop 96).take 16 =
  ((Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields.drop 96).take 16).map encodeField

theorem fieldsSlice96 : (data.fields.drop 96).take 16 = (fieldsSource.drop 96).take 16 :=
  fieldsLeaf96.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields encodeField 96 16)

numeric_data_binding fieldsLeaf112 : (data.fields.drop 112).take 16 =
  ((Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields.drop 112).take 16).map encodeField

theorem fieldsSlice112 : (data.fields.drop 112).take 16 = (fieldsSource.drop 112).take 16 :=
  fieldsLeaf112.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields encodeField 112 16)

numeric_data_binding fieldsLeaf128 : (data.fields.drop 128).take 16 =
  ((Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields.drop 128).take 16).map encodeField

theorem fieldsSlice128 : (data.fields.drop 128).take 16 = (fieldsSource.drop 128).take 16 :=
  fieldsLeaf128.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields encodeField 128 16)

numeric_data_binding fieldsLeaf144 : (data.fields.drop 144).take 16 =
  ((Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields.drop 144).take 16).map encodeField

theorem fieldsSlice144 : (data.fields.drop 144).take 16 = (fieldsSource.drop 144).take 16 :=
  fieldsLeaf144.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields encodeField 144 16)

numeric_data_binding fieldsLeaf160 : (data.fields.drop 160).take 16 =
  ((Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields.drop 160).take 16).map encodeField

theorem fieldsSlice160 : (data.fields.drop 160).take 16 = (fieldsSource.drop 160).take 16 :=
  fieldsLeaf160.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields encodeField 160 16)

numeric_data_binding fieldsLeaf176 : (data.fields.drop 176).take 16 =
  ((Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields.drop 176).take 16).map encodeField

theorem fieldsSlice176 : (data.fields.drop 176).take 16 = (fieldsSource.drop 176).take 16 :=
  fieldsLeaf176.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields encodeField 176 16)

numeric_data_binding fieldsLeaf192 : (data.fields.drop 192).take 16 =
  ((Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields.drop 192).take 16).map encodeField

theorem fieldsSlice192 : (data.fields.drop 192).take 16 = (fieldsSource.drop 192).take 16 :=
  fieldsLeaf192.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields encodeField 192 16)

numeric_data_binding fieldsLeaf208 : (data.fields.drop 208).take 16 =
  ((Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields.drop 208).take 16).map encodeField

theorem fieldsSlice208 : (data.fields.drop 208).take 16 = (fieldsSource.drop 208).take 16 :=
  fieldsLeaf208.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields encodeField 208 16)

numeric_data_binding fieldsLeaf224 : (data.fields.drop 224).take 16 =
  ((Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields.drop 224).take 16).map encodeField

theorem fieldsSlice224 : (data.fields.drop 224).take 16 = (fieldsSource.drop 224).take 16 :=
  fieldsLeaf224.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields encodeField 224 16)

numeric_data_binding fieldsLeaf240 : (data.fields.drop 240).take 16 =
  ((Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields.drop 240).take 16).map encodeField

theorem fieldsSlice240 : (data.fields.drop 240).take 16 = (fieldsSource.drop 240).take 16 :=
  fieldsLeaf240.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields encodeField 240 16)

numeric_data_binding fieldsLeaf256 : (data.fields.drop 256).take 16 =
  ((Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields.drop 256).take 16).map encodeField

theorem fieldsSlice256 : (data.fields.drop 256).take 16 = (fieldsSource.drop 256).take 16 :=
  fieldsLeaf256.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields encodeField 256 16)

numeric_data_binding fieldsLeaf272 : (data.fields.drop 272).take 16 =
  ((Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields.drop 272).take 16).map encodeField

theorem fieldsSlice272 : (data.fields.drop 272).take 16 = (fieldsSource.drop 272).take 16 :=
  fieldsLeaf272.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields encodeField 272 16)

numeric_data_binding fieldsLeaf288 : (data.fields.drop 288).take 16 =
  ((Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields.drop 288).take 16).map encodeField

theorem fieldsSlice288 : (data.fields.drop 288).take 16 = (fieldsSource.drop 288).take 16 :=
  fieldsLeaf288.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields encodeField 288 16)

numeric_data_binding fieldsLeaf304 : (data.fields.drop 304).take 16 =
  ((Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields.drop 304).take 16).map encodeField

theorem fieldsSlice304 : (data.fields.drop 304).take 16 = (fieldsSource.drop 304).take 16 :=
  fieldsLeaf304.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields encodeField 304 16)

numeric_data_binding fieldsLeaf320 : (data.fields.drop 320).take 8 =
  ((Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields.drop 320).take 8).map encodeField

theorem fieldsSlice320 : (data.fields.drop 320).take 8 = (fieldsSource.drop 320).take 8 :=
  fieldsLeaf320.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields encodeField 320 8)

theorem fieldsNode0_32 : (data.fields.drop 0).take 32 = (fieldsSource.drop 0).take 32 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 0 16 16 fieldsSlice0 fieldsSlice16

theorem fieldsNode48_32 : (data.fields.drop 48).take 32 = (fieldsSource.drop 48).take 32 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 48 16 16 fieldsSlice48 fieldsSlice64

theorem fieldsNode32_48 : (data.fields.drop 32).take 48 = (fieldsSource.drop 32).take 48 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 32 16 32 fieldsSlice32 fieldsNode48_32

theorem fieldsNode0_80 : (data.fields.drop 0).take 80 = (fieldsSource.drop 0).take 80 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 0 32 48 fieldsNode0_32 fieldsNode32_48

theorem fieldsNode80_32 : (data.fields.drop 80).take 32 = (fieldsSource.drop 80).take 32 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 80 16 16 fieldsSlice80 fieldsSlice96

theorem fieldsNode128_32 : (data.fields.drop 128).take 32 = (fieldsSource.drop 128).take 32 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 128 16 16 fieldsSlice128 fieldsSlice144

theorem fieldsNode112_48 : (data.fields.drop 112).take 48 = (fieldsSource.drop 112).take 48 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 112 16 32 fieldsSlice112 fieldsNode128_32

theorem fieldsNode80_80 : (data.fields.drop 80).take 80 = (fieldsSource.drop 80).take 80 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 80 32 48 fieldsNode80_32 fieldsNode112_48

theorem fieldsNode0_160 : (data.fields.drop 0).take 160 = (fieldsSource.drop 0).take 160 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 0 80 80 fieldsNode0_80 fieldsNode80_80

theorem fieldsNode160_32 : (data.fields.drop 160).take 32 = (fieldsSource.drop 160).take 32 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 160 16 16 fieldsSlice160 fieldsSlice176

theorem fieldsNode208_32 : (data.fields.drop 208).take 32 = (fieldsSource.drop 208).take 32 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 208 16 16 fieldsSlice208 fieldsSlice224

theorem fieldsNode192_48 : (data.fields.drop 192).take 48 = (fieldsSource.drop 192).take 48 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 192 16 32 fieldsSlice192 fieldsNode208_32

theorem fieldsNode160_80 : (data.fields.drop 160).take 80 = (fieldsSource.drop 160).take 80 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 160 32 48 fieldsNode160_32 fieldsNode192_48

theorem fieldsNode256_32 : (data.fields.drop 256).take 32 = (fieldsSource.drop 256).take 32 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 256 16 16 fieldsSlice256 fieldsSlice272

theorem fieldsNode240_48 : (data.fields.drop 240).take 48 = (fieldsSource.drop 240).take 48 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 240 16 32 fieldsSlice240 fieldsNode256_32

theorem fieldsNode304_24 : (data.fields.drop 304).take 24 = (fieldsSource.drop 304).take 24 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 304 16 8 fieldsSlice304 fieldsSlice320

theorem fieldsNode288_40 : (data.fields.drop 288).take 40 = (fieldsSource.drop 288).take 40 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 288 16 24 fieldsSlice288 fieldsNode304_24

theorem fieldsNode240_88 : (data.fields.drop 240).take 88 = (fieldsSource.drop 240).take 88 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 240 48 40 fieldsNode240_48 fieldsNode288_40

theorem fieldsNode160_168 : (data.fields.drop 160).take 168 = (fieldsSource.drop 160).take 168 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 160 80 88 fieldsNode160_80 fieldsNode240_88

theorem fieldsNode0_328 : (data.fields.drop 0).take 328 = (fieldsSource.drop 0).take 328 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 0 160 168 fieldsNode0_160 fieldsNode160_168

theorem originalFieldsLength : Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields.length = 328 := by decide +kernel

theorem fields_binding : data.fields = fieldsSource :=
  NumericQueryFrameChecks.complete_binding data.fields fieldsSource 328
    (by decide +kernel) (by rw [fieldsSource, List.length_map, originalFieldsLength]) fieldsNode0_328

end Airbender.Compiler.QueryFrameChecks.KeccakUncached
