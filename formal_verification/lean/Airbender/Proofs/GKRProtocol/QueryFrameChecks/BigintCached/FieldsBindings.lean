import Airbender.Proofs.GKRProtocol.QueryFrameChecks.BigintCached.Data
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.QueryFrameChecks.BigintCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def encodeField : Source.EncodedField → NumericPolynomialChecks.Data × NumericPolynomialChecks.Data := (fun field : Source.EncodedField => (NumericPolynomialChecks.encode (field.polynomial Airbender.Compiler.FullArithmeticNative.BigintCached.native.originalProjection), NumericPolynomialChecks.encode (field.polynomial Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement)))

noncomputable def fieldsSource := Airbender.Compiler.QueryFrameNative.BigintCached.native.fields.map encodeField

numeric_data_binding fieldsLeaf0 : (data.fields.drop 0).take 16 =
  ((Airbender.Compiler.QueryFrameNative.BigintCached.native.fields.drop 0).take 16).map encodeField

theorem fieldsSlice0 : (data.fields.drop 0).take 16 = (fieldsSource.drop 0).take 16 :=
  fieldsLeaf0.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.BigintCached.native.fields encodeField 0 16)

numeric_data_binding fieldsLeaf16 : (data.fields.drop 16).take 16 =
  ((Airbender.Compiler.QueryFrameNative.BigintCached.native.fields.drop 16).take 16).map encodeField

theorem fieldsSlice16 : (data.fields.drop 16).take 16 = (fieldsSource.drop 16).take 16 :=
  fieldsLeaf16.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.BigintCached.native.fields encodeField 16 16)

numeric_data_binding fieldsLeaf32 : (data.fields.drop 32).take 16 =
  ((Airbender.Compiler.QueryFrameNative.BigintCached.native.fields.drop 32).take 16).map encodeField

theorem fieldsSlice32 : (data.fields.drop 32).take 16 = (fieldsSource.drop 32).take 16 :=
  fieldsLeaf32.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.BigintCached.native.fields encodeField 32 16)

numeric_data_binding fieldsLeaf48 : (data.fields.drop 48).take 16 =
  ((Airbender.Compiler.QueryFrameNative.BigintCached.native.fields.drop 48).take 16).map encodeField

theorem fieldsSlice48 : (data.fields.drop 48).take 16 = (fieldsSource.drop 48).take 16 :=
  fieldsLeaf48.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.BigintCached.native.fields encodeField 48 16)

numeric_data_binding fieldsLeaf64 : (data.fields.drop 64).take 16 =
  ((Airbender.Compiler.QueryFrameNative.BigintCached.native.fields.drop 64).take 16).map encodeField

theorem fieldsSlice64 : (data.fields.drop 64).take 16 = (fieldsSource.drop 64).take 16 :=
  fieldsLeaf64.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.BigintCached.native.fields encodeField 64 16)

numeric_data_binding fieldsLeaf80 : (data.fields.drop 80).take 16 =
  ((Airbender.Compiler.QueryFrameNative.BigintCached.native.fields.drop 80).take 16).map encodeField

theorem fieldsSlice80 : (data.fields.drop 80).take 16 = (fieldsSource.drop 80).take 16 :=
  fieldsLeaf80.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.BigintCached.native.fields encodeField 80 16)

numeric_data_binding fieldsLeaf96 : (data.fields.drop 96).take 16 =
  ((Airbender.Compiler.QueryFrameNative.BigintCached.native.fields.drop 96).take 16).map encodeField

theorem fieldsSlice96 : (data.fields.drop 96).take 16 = (fieldsSource.drop 96).take 16 :=
  fieldsLeaf96.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.BigintCached.native.fields encodeField 96 16)

numeric_data_binding fieldsLeaf112 : (data.fields.drop 112).take 16 =
  ((Airbender.Compiler.QueryFrameNative.BigintCached.native.fields.drop 112).take 16).map encodeField

theorem fieldsSlice112 : (data.fields.drop 112).take 16 = (fieldsSource.drop 112).take 16 :=
  fieldsLeaf112.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.BigintCached.native.fields encodeField 112 16)

numeric_data_binding fieldsLeaf128 : (data.fields.drop 128).take 16 =
  ((Airbender.Compiler.QueryFrameNative.BigintCached.native.fields.drop 128).take 16).map encodeField

theorem fieldsSlice128 : (data.fields.drop 128).take 16 = (fieldsSource.drop 128).take 16 :=
  fieldsLeaf128.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.BigintCached.native.fields encodeField 128 16)

numeric_data_binding fieldsLeaf144 : (data.fields.drop 144).take 16 =
  ((Airbender.Compiler.QueryFrameNative.BigintCached.native.fields.drop 144).take 16).map encodeField

theorem fieldsSlice144 : (data.fields.drop 144).take 16 = (fieldsSource.drop 144).take 16 :=
  fieldsLeaf144.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.BigintCached.native.fields encodeField 144 16)

numeric_data_binding fieldsLeaf160 : (data.fields.drop 160).take 16 =
  ((Airbender.Compiler.QueryFrameNative.BigintCached.native.fields.drop 160).take 16).map encodeField

theorem fieldsSlice160 : (data.fields.drop 160).take 16 = (fieldsSource.drop 160).take 16 :=
  fieldsLeaf160.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.BigintCached.native.fields encodeField 160 16)

numeric_data_binding fieldsLeaf176 : (data.fields.drop 176).take 16 =
  ((Airbender.Compiler.QueryFrameNative.BigintCached.native.fields.drop 176).take 16).map encodeField

theorem fieldsSlice176 : (data.fields.drop 176).take 16 = (fieldsSource.drop 176).take 16 :=
  fieldsLeaf176.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.BigintCached.native.fields encodeField 176 16)

numeric_data_binding fieldsLeaf192 : (data.fields.drop 192).take 16 =
  ((Airbender.Compiler.QueryFrameNative.BigintCached.native.fields.drop 192).take 16).map encodeField

theorem fieldsSlice192 : (data.fields.drop 192).take 16 = (fieldsSource.drop 192).take 16 :=
  fieldsLeaf192.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.BigintCached.native.fields encodeField 192 16)

numeric_data_binding fieldsLeaf208 : (data.fields.drop 208).take 7 =
  ((Airbender.Compiler.QueryFrameNative.BigintCached.native.fields.drop 208).take 7).map encodeField

theorem fieldsSlice208 : (data.fields.drop 208).take 7 = (fieldsSource.drop 208).take 7 :=
  fieldsLeaf208.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.BigintCached.native.fields encodeField 208 7)

theorem fieldsNode16_32 : (data.fields.drop 16).take 32 = (fieldsSource.drop 16).take 32 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 16 16 16 fieldsSlice16 fieldsSlice32

theorem fieldsNode0_48 : (data.fields.drop 0).take 48 = (fieldsSource.drop 0).take 48 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 0 16 32 fieldsSlice0 fieldsNode16_32

theorem fieldsNode48_32 : (data.fields.drop 48).take 32 = (fieldsSource.drop 48).take 32 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 48 16 16 fieldsSlice48 fieldsSlice64

theorem fieldsNode80_32 : (data.fields.drop 80).take 32 = (fieldsSource.drop 80).take 32 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 80 16 16 fieldsSlice80 fieldsSlice96

theorem fieldsNode48_64 : (data.fields.drop 48).take 64 = (fieldsSource.drop 48).take 64 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 48 32 32 fieldsNode48_32 fieldsNode80_32

theorem fieldsNode0_112 : (data.fields.drop 0).take 112 = (fieldsSource.drop 0).take 112 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 0 48 64 fieldsNode0_48 fieldsNode48_64

theorem fieldsNode128_32 : (data.fields.drop 128).take 32 = (fieldsSource.drop 128).take 32 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 128 16 16 fieldsSlice128 fieldsSlice144

theorem fieldsNode112_48 : (data.fields.drop 112).take 48 = (fieldsSource.drop 112).take 48 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 112 16 32 fieldsSlice112 fieldsNode128_32

theorem fieldsNode160_32 : (data.fields.drop 160).take 32 = (fieldsSource.drop 160).take 32 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 160 16 16 fieldsSlice160 fieldsSlice176

theorem fieldsNode192_23 : (data.fields.drop 192).take 23 = (fieldsSource.drop 192).take 23 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 192 16 7 fieldsSlice192 fieldsSlice208

theorem fieldsNode160_55 : (data.fields.drop 160).take 55 = (fieldsSource.drop 160).take 55 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 160 32 23 fieldsNode160_32 fieldsNode192_23

theorem fieldsNode112_103 : (data.fields.drop 112).take 103 = (fieldsSource.drop 112).take 103 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 112 48 55 fieldsNode112_48 fieldsNode160_55

theorem fieldsNode0_215 : (data.fields.drop 0).take 215 = (fieldsSource.drop 0).take 215 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 0 112 103 fieldsNode0_112 fieldsNode112_103

theorem originalFieldsLength : Airbender.Compiler.QueryFrameNative.BigintCached.native.fields.length = 215 := by decide +kernel

theorem fields_binding : data.fields = fieldsSource :=
  NumericQueryFrameChecks.complete_binding data.fields fieldsSource 215
    (by decide +kernel) (by rw [fieldsSource, List.length_map, originalFieldsLength]) fieldsNode0_215

end Airbender.Compiler.QueryFrameChecks.BigintCached
