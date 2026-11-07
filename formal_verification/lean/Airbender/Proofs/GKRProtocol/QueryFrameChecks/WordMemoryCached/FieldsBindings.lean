import Airbender.Proofs.GKRProtocol.QueryFrameChecks.WordMemoryCached.Data
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.QueryFrameChecks.WordMemoryCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def encodeField : Source.EncodedField → NumericPolynomialChecks.Data × NumericPolynomialChecks.Data := (fun field : Source.EncodedField => (NumericPolynomialChecks.encode (field.polynomial Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.originalProjection), NumericPolynomialChecks.encode (field.polynomial Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement)))

noncomputable def fieldsSource := Airbender.Compiler.QueryFrameNative.WordMemoryCached.native.fields.map encodeField

numeric_data_binding fieldsLeaf0 : (data.fields.drop 0).take 16 =
  ((Airbender.Compiler.QueryFrameNative.WordMemoryCached.native.fields.drop 0).take 16).map encodeField

theorem fieldsSlice0 : (data.fields.drop 0).take 16 = (fieldsSource.drop 0).take 16 :=
  fieldsLeaf0.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.WordMemoryCached.native.fields encodeField 0 16)

numeric_data_binding fieldsLeaf16 : (data.fields.drop 16).take 6 =
  ((Airbender.Compiler.QueryFrameNative.WordMemoryCached.native.fields.drop 16).take 6).map encodeField

theorem fieldsSlice16 : (data.fields.drop 16).take 6 = (fieldsSource.drop 16).take 6 :=
  fieldsLeaf16.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.WordMemoryCached.native.fields encodeField 16 6)

theorem fieldsNode0_22 : (data.fields.drop 0).take 22 = (fieldsSource.drop 0).take 22 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 0 16 6 fieldsSlice0 fieldsSlice16

theorem originalFieldsLength : Airbender.Compiler.QueryFrameNative.WordMemoryCached.native.fields.length = 22 := by decide +kernel

theorem fields_binding : data.fields = fieldsSource :=
  NumericQueryFrameChecks.complete_binding data.fields fieldsSource 22
    (by decide +kernel) (by rw [fieldsSource, List.length_map, originalFieldsLength]) fieldsNode0_22

end Airbender.Compiler.QueryFrameChecks.WordMemoryCached
