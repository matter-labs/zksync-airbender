import Airbender.Proofs.GKRProtocol.QueryFrameChecks.SubwordMemoryUncached.Data
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.QueryFrameChecks.SubwordMemoryUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def encodeField : Source.EncodedField → NumericPolynomialChecks.Data × NumericPolynomialChecks.Data := (fun field : Source.EncodedField => (NumericPolynomialChecks.encode (field.polynomial Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.originalProjection), NumericPolynomialChecks.encode (field.polynomial Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement)))

noncomputable def fieldsSource := Airbender.Compiler.QueryFrameNative.SubwordMemoryUncached.native.fields.map encodeField

numeric_data_binding fieldsLeaf0 : (data.fields.drop 0).take 16 =
  ((Airbender.Compiler.QueryFrameNative.SubwordMemoryUncached.native.fields.drop 0).take 16).map encodeField

theorem fieldsSlice0 : (data.fields.drop 0).take 16 = (fieldsSource.drop 0).take 16 :=
  fieldsLeaf0.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.SubwordMemoryUncached.native.fields encodeField 0 16)

numeric_data_binding fieldsLeaf16 : (data.fields.drop 16).take 16 =
  ((Airbender.Compiler.QueryFrameNative.SubwordMemoryUncached.native.fields.drop 16).take 16).map encodeField

theorem fieldsSlice16 : (data.fields.drop 16).take 16 = (fieldsSource.drop 16).take 16 :=
  fieldsLeaf16.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.SubwordMemoryUncached.native.fields encodeField 16 16)

numeric_data_binding fieldsLeaf32 : (data.fields.drop 32).take 1 =
  ((Airbender.Compiler.QueryFrameNative.SubwordMemoryUncached.native.fields.drop 32).take 1).map encodeField

theorem fieldsSlice32 : (data.fields.drop 32).take 1 = (fieldsSource.drop 32).take 1 :=
  fieldsLeaf32.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.SubwordMemoryUncached.native.fields encodeField 32 1)

theorem fieldsNode16_17 : (data.fields.drop 16).take 17 = (fieldsSource.drop 16).take 17 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 16 16 1 fieldsSlice16 fieldsSlice32

theorem fieldsNode0_33 : (data.fields.drop 0).take 33 = (fieldsSource.drop 0).take 33 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 0 16 17 fieldsSlice0 fieldsNode16_17

theorem originalFieldsLength : Airbender.Compiler.QueryFrameNative.SubwordMemoryUncached.native.fields.length = 33 := by decide +kernel

theorem fields_binding : data.fields = fieldsSource :=
  NumericQueryFrameChecks.complete_binding data.fields fieldsSource 33
    (by decide +kernel) (by rw [fieldsSource, List.length_map, originalFieldsLength]) fieldsNode0_33

end Airbender.Compiler.QueryFrameChecks.SubwordMemoryUncached
