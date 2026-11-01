import Airbender.Proofs.GKRProtocol.QueryFrameChecks.JumpBranchCached.Data
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.QueryFrameChecks.JumpBranchCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def encodeField : Source.EncodedField → NumericPolynomialChecks.Data × NumericPolynomialChecks.Data := (fun field : Source.EncodedField => (NumericPolynomialChecks.encode (field.polynomial Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.originalProjection), NumericPolynomialChecks.encode (field.polynomial Airbender.Compiler.LookupNative.JumpBranchCached.native.sourcePlacement)))

noncomputable def fieldsSource := Airbender.Compiler.QueryFrameNative.JumpBranchCached.native.fields.map encodeField

numeric_data_binding fieldsLeaf0 : (data.fields.drop 0).take 16 =
  ((Airbender.Compiler.QueryFrameNative.JumpBranchCached.native.fields.drop 0).take 16).map encodeField

theorem fieldsSlice0 : (data.fields.drop 0).take 16 = (fieldsSource.drop 0).take 16 :=
  fieldsLeaf0.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.JumpBranchCached.native.fields encodeField 0 16)

numeric_data_binding fieldsLeaf16 : (data.fields.drop 16).take 16 =
  ((Airbender.Compiler.QueryFrameNative.JumpBranchCached.native.fields.drop 16).take 16).map encodeField

theorem fieldsSlice16 : (data.fields.drop 16).take 16 = (fieldsSource.drop 16).take 16 :=
  fieldsLeaf16.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.JumpBranchCached.native.fields encodeField 16 16)

numeric_data_binding fieldsLeaf32 : (data.fields.drop 32).take 16 =
  ((Airbender.Compiler.QueryFrameNative.JumpBranchCached.native.fields.drop 32).take 16).map encodeField

theorem fieldsSlice32 : (data.fields.drop 32).take 16 = (fieldsSource.drop 32).take 16 :=
  fieldsLeaf32.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.JumpBranchCached.native.fields encodeField 32 16)

numeric_data_binding fieldsLeaf48 : (data.fields.drop 48).take 7 =
  ((Airbender.Compiler.QueryFrameNative.JumpBranchCached.native.fields.drop 48).take 7).map encodeField

theorem fieldsSlice48 : (data.fields.drop 48).take 7 = (fieldsSource.drop 48).take 7 :=
  fieldsLeaf48.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.QueryFrameNative.JumpBranchCached.native.fields encodeField 48 7)

theorem fieldsNode0_32 : (data.fields.drop 0).take 32 = (fieldsSource.drop 0).take 32 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 0 16 16 fieldsSlice0 fieldsSlice16

theorem fieldsNode32_23 : (data.fields.drop 32).take 23 = (fieldsSource.drop 32).take 23 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 32 16 7 fieldsSlice32 fieldsSlice48

theorem fieldsNode0_55 : (data.fields.drop 0).take 55 = (fieldsSource.drop 0).take 55 :=
  NumericQueryFrameChecks.merge_bindings data.fields fieldsSource 0 32 23 fieldsNode0_32 fieldsNode32_23

theorem originalFieldsLength : Airbender.Compiler.QueryFrameNative.JumpBranchCached.native.fields.length = 55 := by decide +kernel

theorem fields_binding : data.fields = fieldsSource :=
  NumericQueryFrameChecks.complete_binding data.fields fieldsSource 55
    (by decide +kernel) (by rw [fieldsSource, List.length_map, originalFieldsLength]) fieldsNode0_55

end Airbender.Compiler.QueryFrameChecks.JumpBranchCached
