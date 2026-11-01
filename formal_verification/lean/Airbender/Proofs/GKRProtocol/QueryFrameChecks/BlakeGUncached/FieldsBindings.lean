import Airbender.Proofs.GKRProtocol.QueryFrameChecks.BlakeGUncached.Data
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.QueryFrameChecks.BlakeGUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def encodeField : Source.EncodedField → NumericPolynomialChecks.Data × NumericPolynomialChecks.Data := (fun field : Source.EncodedField => (NumericPolynomialChecks.encode (field.polynomial Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.originalProjection), NumericPolynomialChecks.encode (field.polynomial Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement)))

noncomputable def fieldsSource := Airbender.Compiler.QueryFrameNative.BlakeGUncached.native.fields.map encodeField

numeric_data_binding fieldsLeaf0 : (data.fields.drop 0).take 16 =
  ((Airbender.Compiler.QueryFrameNative.BlakeGUncached.native.fields.drop 0).take 16).map encodeField

theorem fieldsSlice0 : (data.fields.drop 0).take 16 = (fieldsSource.drop 0).take 16 :=
  fieldsLeaf0.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.BlakeGUncached.native.fields encodeField 0 16)

numeric_data_binding fieldsLeaf16 : (data.fields.drop 16).take 16 =
  ((Airbender.Compiler.QueryFrameNative.BlakeGUncached.native.fields.drop 16).take 16).map encodeField

theorem fieldsSlice16 : (data.fields.drop 16).take 16 = (fieldsSource.drop 16).take 16 :=
  fieldsLeaf16.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.BlakeGUncached.native.fields encodeField 16 16)

numeric_data_binding fieldsLeaf32 : (data.fields.drop 32).take 16 =
  ((Airbender.Compiler.QueryFrameNative.BlakeGUncached.native.fields.drop 32).take 16).map encodeField

theorem fieldsSlice32 : (data.fields.drop 32).take 16 = (fieldsSource.drop 32).take 16 :=
  fieldsLeaf32.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.BlakeGUncached.native.fields encodeField 32 16)

numeric_data_binding fieldsLeaf48 : (data.fields.drop 48).take 16 =
  ((Airbender.Compiler.QueryFrameNative.BlakeGUncached.native.fields.drop 48).take 16).map encodeField

theorem fieldsSlice48 : (data.fields.drop 48).take 16 = (fieldsSource.drop 48).take 16 :=
  fieldsLeaf48.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.BlakeGUncached.native.fields encodeField 48 16)

numeric_data_binding fieldsLeaf64 : (data.fields.drop 64).take 16 =
  ((Airbender.Compiler.QueryFrameNative.BlakeGUncached.native.fields.drop 64).take 16).map encodeField

theorem fieldsSlice64 : (data.fields.drop 64).take 16 = (fieldsSource.drop 64).take 16 :=
  fieldsLeaf64.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.BlakeGUncached.native.fields encodeField 64 16)

numeric_data_binding fieldsLeaf80 : (data.fields.drop 80).take 16 =
  ((Airbender.Compiler.QueryFrameNative.BlakeGUncached.native.fields.drop 80).take 16).map encodeField

theorem fieldsSlice80 : (data.fields.drop 80).take 16 = (fieldsSource.drop 80).take 16 :=
  fieldsLeaf80.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.BlakeGUncached.native.fields encodeField 80 16)

numeric_data_binding fieldsLeaf96 : (data.fields.drop 96).take 16 =
  ((Airbender.Compiler.QueryFrameNative.BlakeGUncached.native.fields.drop 96).take 16).map encodeField

theorem fieldsSlice96 : (data.fields.drop 96).take 16 = (fieldsSource.drop 96).take 16 :=
  fieldsLeaf96.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.BlakeGUncached.native.fields encodeField 96 16)

numeric_data_binding fieldsLeaf112 : (data.fields.drop 112).take 16 =
  ((Airbender.Compiler.QueryFrameNative.BlakeGUncached.native.fields.drop 112).take 16).map encodeField

theorem fieldsSlice112 : (data.fields.drop 112).take 16 = (fieldsSource.drop 112).take 16 :=
  fieldsLeaf112.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.BlakeGUncached.native.fields encodeField 112 16)

numeric_data_binding fieldsLeaf128 : (data.fields.drop 128).take 16 =
  ((Airbender.Compiler.QueryFrameNative.BlakeGUncached.native.fields.drop 128).take 16).map encodeField

theorem fieldsSlice128 : (data.fields.drop 128).take 16 = (fieldsSource.drop 128).take 16 :=
  fieldsLeaf128.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.BlakeGUncached.native.fields encodeField 128 16)

numeric_data_binding fieldsLeaf144 : (data.fields.drop 144).take 16 =
  ((Airbender.Compiler.QueryFrameNative.BlakeGUncached.native.fields.drop 144).take 16).map encodeField

theorem fieldsSlice144 : (data.fields.drop 144).take 16 = (fieldsSource.drop 144).take 16 :=
  fieldsLeaf144.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.BlakeGUncached.native.fields encodeField 144 16)

numeric_data_binding fieldsLeaf160 : (data.fields.drop 160).take 11 =
  ((Airbender.Compiler.QueryFrameNative.BlakeGUncached.native.fields.drop 160).take 11).map encodeField

theorem fieldsSlice160 : (data.fields.drop 160).take 11 = (fieldsSource.drop 160).take 11 :=
  fieldsLeaf160.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.BlakeGUncached.native.fields encodeField 160 11)

theorem fieldsNode0_32 : (data.fields.drop 0).take 32 = (fieldsSource.drop 0).take 32 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 0 16 16 fieldsSlice0 fieldsSlice16

theorem fieldsNode48_32 : (data.fields.drop 48).take 32 = (fieldsSource.drop 48).take 32 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 48 16 16 fieldsSlice48 fieldsSlice64

theorem fieldsNode32_48 : (data.fields.drop 32).take 48 = (fieldsSource.drop 32).take 48 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 32 16 32 fieldsSlice32 fieldsNode48_32

theorem fieldsNode0_80 : (data.fields.drop 0).take 80 = (fieldsSource.drop 0).take 80 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 0 32 48 fieldsNode0_32 fieldsNode32_48

theorem fieldsNode96_32 : (data.fields.drop 96).take 32 = (fieldsSource.drop 96).take 32 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 96 16 16 fieldsSlice96 fieldsSlice112

theorem fieldsNode80_48 : (data.fields.drop 80).take 48 = (fieldsSource.drop 80).take 48 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 80 16 32 fieldsSlice80 fieldsNode96_32

theorem fieldsNode144_27 : (data.fields.drop 144).take 27 = (fieldsSource.drop 144).take 27 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 144 16 11 fieldsSlice144 fieldsSlice160

theorem fieldsNode128_43 : (data.fields.drop 128).take 43 = (fieldsSource.drop 128).take 43 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 128 16 27 fieldsSlice128 fieldsNode144_27

theorem fieldsNode80_91 : (data.fields.drop 80).take 91 = (fieldsSource.drop 80).take 91 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 80 48 43 fieldsNode80_48 fieldsNode128_43

theorem fieldsNode0_171 : (data.fields.drop 0).take 171 = (fieldsSource.drop 0).take 171 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 0 80 91 fieldsNode0_80 fieldsNode80_91

theorem originalFieldsLength : Airbender.Compiler.QueryFrameNative.BlakeGUncached.native.fields.length = 171 := by decide +kernel

theorem fields_binding : data.fields = fieldsSource :=
  NumericQueryFrameChecks.complete_binding data.fields fieldsSource 171
    (by decide +kernel) (by rw [fieldsSource, List.length_map, originalFieldsLength]) fieldsNode0_171

end Airbender.Compiler.QueryFrameChecks.BlakeGUncached
