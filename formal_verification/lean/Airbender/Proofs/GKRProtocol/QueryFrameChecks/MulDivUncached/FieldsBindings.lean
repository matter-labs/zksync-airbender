import Airbender.Proofs.GKRProtocol.QueryFrameChecks.MulDivUncached.Data
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.QueryFrameChecks.MulDivUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def encodeField : Source.EncodedField → NumericPolynomialChecks.Data × NumericPolynomialChecks.Data := (fun field : Source.EncodedField => (NumericPolynomialChecks.encode (field.polynomial Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.originalProjection), NumericPolynomialChecks.encode (field.polynomial Airbender.Compiler.LookupNative.MulDivUncached.native.sourcePlacement)))

noncomputable def fieldsSource := Airbender.Compiler.QueryFrameNative.MulDivUncached.native.fields.map encodeField

numeric_data_binding fieldsLeaf0 : (data.fields.drop 0).take 16 =
  ((Airbender.Compiler.QueryFrameNative.MulDivUncached.native.fields.drop 0).take 16).map encodeField

theorem fieldsSlice0 : (data.fields.drop 0).take 16 = (fieldsSource.drop 0).take 16 :=
  fieldsLeaf0.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.MulDivUncached.native.fields encodeField 0 16)

numeric_data_binding fieldsLeaf16 : (data.fields.drop 16).take 16 =
  ((Airbender.Compiler.QueryFrameNative.MulDivUncached.native.fields.drop 16).take 16).map encodeField

theorem fieldsSlice16 : (data.fields.drop 16).take 16 = (fieldsSource.drop 16).take 16 :=
  fieldsLeaf16.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.MulDivUncached.native.fields encodeField 16 16)

numeric_data_binding fieldsLeaf32 : (data.fields.drop 32).take 16 =
  ((Airbender.Compiler.QueryFrameNative.MulDivUncached.native.fields.drop 32).take 16).map encodeField

theorem fieldsSlice32 : (data.fields.drop 32).take 16 = (fieldsSource.drop 32).take 16 :=
  fieldsLeaf32.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.MulDivUncached.native.fields encodeField 32 16)

numeric_data_binding fieldsLeaf48 : (data.fields.drop 48).take 16 =
  ((Airbender.Compiler.QueryFrameNative.MulDivUncached.native.fields.drop 48).take 16).map encodeField

theorem fieldsSlice48 : (data.fields.drop 48).take 16 = (fieldsSource.drop 48).take 16 :=
  fieldsLeaf48.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.MulDivUncached.native.fields encodeField 48 16)

numeric_data_binding fieldsLeaf64 : (data.fields.drop 64).take 16 =
  ((Airbender.Compiler.QueryFrameNative.MulDivUncached.native.fields.drop 64).take 16).map encodeField

theorem fieldsSlice64 : (data.fields.drop 64).take 16 = (fieldsSource.drop 64).take 16 :=
  fieldsLeaf64.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.MulDivUncached.native.fields encodeField 64 16)

numeric_data_binding fieldsLeaf80 : (data.fields.drop 80).take 10 =
  ((Airbender.Compiler.QueryFrameNative.MulDivUncached.native.fields.drop 80).take 10).map encodeField

theorem fieldsSlice80 : (data.fields.drop 80).take 10 = (fieldsSource.drop 80).take 10 :=
  fieldsLeaf80.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.MulDivUncached.native.fields encodeField 80 10)

theorem fieldsNode16_32 : (data.fields.drop 16).take 32 = (fieldsSource.drop 16).take 32 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 16 16 16 fieldsSlice16 fieldsSlice32

theorem fieldsNode0_48 : (data.fields.drop 0).take 48 = (fieldsSource.drop 0).take 48 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 0 16 32 fieldsSlice0 fieldsNode16_32

theorem fieldsNode64_26 : (data.fields.drop 64).take 26 = (fieldsSource.drop 64).take 26 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 64 16 10 fieldsSlice64 fieldsSlice80

theorem fieldsNode48_42 : (data.fields.drop 48).take 42 = (fieldsSource.drop 48).take 42 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 48 16 26 fieldsSlice48 fieldsNode64_26

theorem fieldsNode0_90 : (data.fields.drop 0).take 90 = (fieldsSource.drop 0).take 90 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 0 48 42 fieldsNode0_48 fieldsNode48_42

theorem originalFieldsLength : Airbender.Compiler.QueryFrameNative.MulDivUncached.native.fields.length = 90 := by decide +kernel

theorem fields_binding : data.fields = fieldsSource :=
  NumericQueryFrameChecks.complete_binding data.fields fieldsSource 90
    (by decide +kernel) (by rw [fieldsSource, List.length_map, originalFieldsLength]) fieldsNode0_90

end Airbender.Compiler.QueryFrameChecks.MulDivUncached
