import Airbender.Proofs.GKRProtocol.QueryFrameChecks.ShiftBinopCached.Data
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.QueryFrameChecks.ShiftBinopCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def encodeField : Source.EncodedField → NumericPolynomialChecks.Data × NumericPolynomialChecks.Data := (fun field : Source.EncodedField => (NumericPolynomialChecks.encode (field.polynomial Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.originalProjection), NumericPolynomialChecks.encode (field.polynomial Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement)))

noncomputable def fieldsSource := Airbender.Compiler.QueryFrameNative.ShiftBinopCached.native.fields.map encodeField

numeric_data_binding fieldsLeaf0 : (data.fields.drop 0).take 16 =
  ((Airbender.Compiler.QueryFrameNative.ShiftBinopCached.native.fields.drop 0).take 16).map encodeField

theorem fieldsSlice0 : (data.fields.drop 0).take 16 = (fieldsSource.drop 0).take 16 :=
  fieldsLeaf0.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.ShiftBinopCached.native.fields encodeField 0 16)

numeric_data_binding fieldsLeaf16 : (data.fields.drop 16).take 16 =
  ((Airbender.Compiler.QueryFrameNative.ShiftBinopCached.native.fields.drop 16).take 16).map encodeField

theorem fieldsSlice16 : (data.fields.drop 16).take 16 = (fieldsSource.drop 16).take 16 :=
  fieldsLeaf16.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.ShiftBinopCached.native.fields encodeField 16 16)

numeric_data_binding fieldsLeaf32 : (data.fields.drop 32).take 16 =
  ((Airbender.Compiler.QueryFrameNative.ShiftBinopCached.native.fields.drop 32).take 16).map encodeField

theorem fieldsSlice32 : (data.fields.drop 32).take 16 = (fieldsSource.drop 32).take 16 :=
  fieldsLeaf32.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.ShiftBinopCached.native.fields encodeField 32 16)

numeric_data_binding fieldsLeaf48 : (data.fields.drop 48).take 15 =
  ((Airbender.Compiler.QueryFrameNative.ShiftBinopCached.native.fields.drop 48).take 15).map encodeField

theorem fieldsSlice48 : (data.fields.drop 48).take 15 = (fieldsSource.drop 48).take 15 :=
  fieldsLeaf48.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.ShiftBinopCached.native.fields encodeField 48 15)

theorem fieldsNode0_32 : (data.fields.drop 0).take 32 = (fieldsSource.drop 0).take 32 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 0 16 16 fieldsSlice0 fieldsSlice16

theorem fieldsNode32_31 : (data.fields.drop 32).take 31 = (fieldsSource.drop 32).take 31 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 32 16 15 fieldsSlice32 fieldsSlice48

theorem fieldsNode0_63 : (data.fields.drop 0).take 63 = (fieldsSource.drop 0).take 63 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 0 32 31 fieldsNode0_32 fieldsNode32_31

theorem originalFieldsLength : Airbender.Compiler.QueryFrameNative.ShiftBinopCached.native.fields.length = 63 := by decide +kernel

theorem fields_binding : data.fields = fieldsSource :=
  NumericQueryFrameChecks.complete_binding data.fields fieldsSource 63
    (by decide +kernel) (by rw [fieldsSource, List.length_map, originalFieldsLength]) fieldsNode0_63

end Airbender.Compiler.QueryFrameChecks.ShiftBinopCached
