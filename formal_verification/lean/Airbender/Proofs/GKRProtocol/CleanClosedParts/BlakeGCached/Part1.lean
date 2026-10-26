import Airbender.Proofs.GKRProtocol.CleanClosedParts.BlakeGCached.Shared

namespace Airbender.Compiler.CleanClosedNative.BlakeGCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

theorem generic_lookup8
    (sourceValue : Fin 113 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BlakeGCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BlakeGCached.native.assigned (Airbender.Compiler.HelperValidityNative.BlakeGCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BlakeGCached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.genericExpressions8).Contains (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BlakeGCached.native.genericQueries.get ⟨8, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.BlakeGCached.native.genericQueries ⟨8, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BlakeGCached.native.field8_0.source ∈ Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields ⟨72, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeGCached.native.field8_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.generic_value8_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BlakeGCached.native.field8_1.source ∈ Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields ⟨73, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeGCached.native.field8_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.generic_value8_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BlakeGCached.native.field8_2.source ∈ Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields ⟨74, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeGCached.native.field8_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.generic_value8_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.BlakeGCached.native.field8_3.source ∈ Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields ⟨75, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeGCached.native.field8_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.generic_value8_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.BlakeGCached.native.field8_4.source ∈ Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields ⟨76, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeGCached.native.field8_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.generic_value8_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.BlakeGCached.native.field8_5.source ∈ Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields ⟨77, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeGCached.native.field8_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.generic_value8_5 physical data arithmetic).trans transported5
  have present6 : Airbender.Compiler.LookupNative.BlakeGCached.native.field8_6.source ∈ Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields ⟨78, by decide⟩
  have transported6 := Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeGCached.native.field8_6.source present6
  have same6 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.generic_value8_6 physical data arithmetic).trans transported6
  have present7 : Airbender.Compiler.LookupNative.BlakeGCached.native.field8_7.source ∈ Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields ⟨79, by decide⟩
  have transported7 := Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeGCached.native.field8_7.source present7
  have same7 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.generic_value8_7 physical data arithmetic).trans transported7
  have present8 : Airbender.Compiler.LookupNative.BlakeGCached.native.field8_8.source ∈ Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields ⟨80, by decide⟩
  have transported8 := Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeGCached.native.field8_8.source present8
  have same8 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.generic_value8_8 physical data arithmetic).trans transported8
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BlakeGCached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BlakeGCached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Blake2G" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.genericExpressions8, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BlakeGCached.native.model.Contains Airbender.Compiler.TableNative.BlakeGCached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression8_0.eval (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression8_1.eval (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression8_2.eval (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression8_3.eval (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression8_4.eval (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression8_5.eval (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression8_6.eval (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression8_7.eval (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression8_8.eval (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5, same6, same7, same8]
  exact valid

theorem generic_lookup9
    (sourceValue : Fin 113 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BlakeGCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BlakeGCached.native.assigned (Airbender.Compiler.HelperValidityNative.BlakeGCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BlakeGCached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.genericExpressions9).Contains (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BlakeGCached.native.genericQueries.get ⟨9, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.BlakeGCached.native.genericQueries ⟨9, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BlakeGCached.native.field9_0.source ∈ Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields ⟨81, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeGCached.native.field9_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.generic_value9_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BlakeGCached.native.field9_1.source ∈ Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields ⟨82, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeGCached.native.field9_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.generic_value9_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BlakeGCached.native.field9_2.source ∈ Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields ⟨83, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeGCached.native.field9_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.generic_value9_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.BlakeGCached.native.field9_3.source ∈ Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields ⟨84, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeGCached.native.field9_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.generic_value9_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.BlakeGCached.native.field9_4.source ∈ Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields ⟨85, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeGCached.native.field9_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.generic_value9_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.BlakeGCached.native.field9_5.source ∈ Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields ⟨86, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeGCached.native.field9_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.generic_value9_5 physical data arithmetic).trans transported5
  have present6 : Airbender.Compiler.LookupNative.BlakeGCached.native.field9_6.source ∈ Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields ⟨87, by decide⟩
  have transported6 := Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeGCached.native.field9_6.source present6
  have same6 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.generic_value9_6 physical data arithmetic).trans transported6
  have present7 : Airbender.Compiler.LookupNative.BlakeGCached.native.field9_7.source ∈ Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields ⟨88, by decide⟩
  have transported7 := Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeGCached.native.field9_7.source present7
  have same7 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.generic_value9_7 physical data arithmetic).trans transported7
  have present8 : Airbender.Compiler.LookupNative.BlakeGCached.native.field9_8.source ∈ Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields ⟨89, by decide⟩
  have transported8 := Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeGCached.native.field9_8.source present8
  have same8 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.generic_value9_8 physical data arithmetic).trans transported8
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BlakeGCached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BlakeGCached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Blake2G" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.genericExpressions9, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BlakeGCached.native.model.Contains Airbender.Compiler.TableNative.BlakeGCached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression9_0.eval (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression9_1.eval (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression9_2.eval (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression9_3.eval (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression9_4.eval (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression9_5.eval (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression9_6.eval (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression9_7.eval (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression9_8.eval (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5, same6, same7, same8]
  exact valid

theorem generic_lookup10
    (sourceValue : Fin 113 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BlakeGCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BlakeGCached.native.assigned (Airbender.Compiler.HelperValidityNative.BlakeGCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BlakeGCached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.genericExpressions10).Contains (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BlakeGCached.native.genericQueries.get ⟨10, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.BlakeGCached.native.genericQueries ⟨10, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BlakeGCached.native.field10_0.source ∈ Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields ⟨90, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeGCached.native.field10_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.generic_value10_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BlakeGCached.native.field10_1.source ∈ Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields ⟨91, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeGCached.native.field10_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.generic_value10_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BlakeGCached.native.field10_2.source ∈ Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields ⟨92, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeGCached.native.field10_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.generic_value10_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.BlakeGCached.native.field10_3.source ∈ Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields ⟨93, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeGCached.native.field10_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.generic_value10_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.BlakeGCached.native.field10_4.source ∈ Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields ⟨94, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeGCached.native.field10_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.generic_value10_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.BlakeGCached.native.field10_5.source ∈ Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields ⟨95, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeGCached.native.field10_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.generic_value10_5 physical data arithmetic).trans transported5
  have present6 : Airbender.Compiler.LookupNative.BlakeGCached.native.field10_6.source ∈ Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields ⟨96, by decide⟩
  have transported6 := Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeGCached.native.field10_6.source present6
  have same6 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.generic_value10_6 physical data arithmetic).trans transported6
  have present7 : Airbender.Compiler.LookupNative.BlakeGCached.native.field10_7.source ∈ Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields ⟨97, by decide⟩
  have transported7 := Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeGCached.native.field10_7.source present7
  have same7 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.generic_value10_7 physical data arithmetic).trans transported7
  have present8 : Airbender.Compiler.LookupNative.BlakeGCached.native.field10_8.source ∈ Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields ⟨98, by decide⟩
  have transported8 := Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeGCached.native.field10_8.source present8
  have same8 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.generic_value10_8 physical data arithmetic).trans transported8
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BlakeGCached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BlakeGCached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Blake2G" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.genericExpressions10, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BlakeGCached.native.model.Contains Airbender.Compiler.TableNative.BlakeGCached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression10_0.eval (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression10_1.eval (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression10_2.eval (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression10_3.eval (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression10_4.eval (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression10_5.eval (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression10_6.eval (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression10_7.eval (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression10_8.eval (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5, same6, same7, same8]
  exact valid

theorem generic_lookup11
    (sourceValue : Fin 113 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BlakeGCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BlakeGCached.native.assigned (Airbender.Compiler.HelperValidityNative.BlakeGCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BlakeGCached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.genericExpressions11).Contains (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BlakeGCached.native.genericQueries.get ⟨11, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.BlakeGCached.native.genericQueries ⟨11, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BlakeGCached.native.field11_0.source ∈ Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields ⟨99, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeGCached.native.field11_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.generic_value11_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BlakeGCached.native.field11_1.source ∈ Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields ⟨100, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeGCached.native.field11_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.generic_value11_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BlakeGCached.native.field11_2.source ∈ Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields ⟨101, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeGCached.native.field11_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.generic_value11_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.BlakeGCached.native.field11_3.source ∈ Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields ⟨102, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeGCached.native.field11_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.generic_value11_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.BlakeGCached.native.field11_4.source ∈ Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields ⟨103, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeGCached.native.field11_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.generic_value11_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.BlakeGCached.native.field11_5.source ∈ Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields ⟨104, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeGCached.native.field11_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.generic_value11_5 physical data arithmetic).trans transported5
  have present6 : Airbender.Compiler.LookupNative.BlakeGCached.native.field11_6.source ∈ Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields ⟨105, by decide⟩
  have transported6 := Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeGCached.native.field11_6.source present6
  have same6 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.generic_value11_6 physical data arithmetic).trans transported6
  have present7 : Airbender.Compiler.LookupNative.BlakeGCached.native.field11_7.source ∈ Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields ⟨106, by decide⟩
  have transported7 := Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeGCached.native.field11_7.source present7
  have same7 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.generic_value11_7 physical data arithmetic).trans transported7
  have present8 : Airbender.Compiler.LookupNative.BlakeGCached.native.field11_8.source ∈ Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields ⟨107, by decide⟩
  have transported8 := Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeGCached.native.field11_8.source present8
  have same8 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.generic_value11_8 physical data arithmetic).trans transported8
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BlakeGCached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BlakeGCached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Blake2G" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.genericExpressions11, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BlakeGCached.native.model.Contains Airbender.Compiler.TableNative.BlakeGCached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression11_0.eval (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression11_1.eval (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression11_2.eval (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression11_3.eval (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression11_4.eval (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression11_5.eval (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression11_6.eval (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression11_7.eval (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression11_8.eval (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5, same6, same7, same8]
  exact valid

theorem generic_lookup12
    (sourceValue : Fin 113 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BlakeGCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BlakeGCached.native.assigned (Airbender.Compiler.HelperValidityNative.BlakeGCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BlakeGCached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.genericExpressions12).Contains (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BlakeGCached.native.genericQueries.get ⟨12, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.BlakeGCached.native.genericQueries ⟨12, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BlakeGCached.native.field12_0.source ∈ Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields ⟨108, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeGCached.native.field12_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.generic_value12_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BlakeGCached.native.field12_1.source ∈ Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields ⟨109, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeGCached.native.field12_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.generic_value12_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BlakeGCached.native.field12_2.source ∈ Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields ⟨110, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeGCached.native.field12_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.generic_value12_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.BlakeGCached.native.field12_3.source ∈ Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields ⟨111, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeGCached.native.field12_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.generic_value12_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.BlakeGCached.native.field12_4.source ∈ Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields ⟨112, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeGCached.native.field12_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.generic_value12_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.BlakeGCached.native.field12_5.source ∈ Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields ⟨113, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeGCached.native.field12_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.generic_value12_5 physical data arithmetic).trans transported5
  have present6 : Airbender.Compiler.LookupNative.BlakeGCached.native.field12_6.source ∈ Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields ⟨114, by decide⟩
  have transported6 := Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeGCached.native.field12_6.source present6
  have same6 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.generic_value12_6 physical data arithmetic).trans transported6
  have present7 : Airbender.Compiler.LookupNative.BlakeGCached.native.field12_7.source ∈ Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields ⟨115, by decide⟩
  have transported7 := Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeGCached.native.field12_7.source present7
  have same7 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.generic_value12_7 physical data arithmetic).trans transported7
  have present8 : Airbender.Compiler.LookupNative.BlakeGCached.native.field12_8.source ∈ Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields ⟨116, by decide⟩
  have transported8 := Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeGCached.native.field12_8.source present8
  have same8 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.generic_value12_8 physical data arithmetic).trans transported8
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BlakeGCached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BlakeGCached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Blake2G" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.genericExpressions12, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BlakeGCached.native.model.Contains Airbender.Compiler.TableNative.BlakeGCached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression12_0.eval (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression12_1.eval (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression12_2.eval (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression12_3.eval (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression12_4.eval (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression12_5.eval (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression12_6.eval (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression12_7.eval (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression12_8.eval (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5, same6, same7, same8]
  exact valid

theorem generic_lookup13
    (sourceValue : Fin 113 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BlakeGCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BlakeGCached.native.assigned (Airbender.Compiler.HelperValidityNative.BlakeGCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BlakeGCached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.genericExpressions13).Contains (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BlakeGCached.native.genericQueries.get ⟨13, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.BlakeGCached.native.genericQueries ⟨13, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BlakeGCached.native.field13_0.source ∈ Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields ⟨117, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeGCached.native.field13_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.generic_value13_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BlakeGCached.native.field13_1.source ∈ Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields ⟨118, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeGCached.native.field13_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.generic_value13_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BlakeGCached.native.field13_2.source ∈ Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields ⟨119, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeGCached.native.field13_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.generic_value13_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.BlakeGCached.native.field13_3.source ∈ Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields ⟨120, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeGCached.native.field13_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.generic_value13_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.BlakeGCached.native.field13_4.source ∈ Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields ⟨121, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeGCached.native.field13_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.generic_value13_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.BlakeGCached.native.field13_5.source ∈ Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields ⟨122, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeGCached.native.field13_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.generic_value13_5 physical data arithmetic).trans transported5
  have present6 : Airbender.Compiler.LookupNative.BlakeGCached.native.field13_6.source ∈ Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields ⟨123, by decide⟩
  have transported6 := Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeGCached.native.field13_6.source present6
  have same6 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.generic_value13_6 physical data arithmetic).trans transported6
  have present7 : Airbender.Compiler.LookupNative.BlakeGCached.native.field13_7.source ∈ Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields ⟨124, by decide⟩
  have transported7 := Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeGCached.native.field13_7.source present7
  have same7 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.generic_value13_7 physical data arithmetic).trans transported7
  have present8 : Airbender.Compiler.LookupNative.BlakeGCached.native.field13_8.source ∈ Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields ⟨125, by decide⟩
  have transported8 := Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeGCached.native.field13_8.source present8
  have same8 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.generic_value13_8 physical data arithmetic).trans transported8
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BlakeGCached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BlakeGCached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Blake2G" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.genericExpressions13, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BlakeGCached.native.model.Contains Airbender.Compiler.TableNative.BlakeGCached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression13_0.eval (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression13_1.eval (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression13_2.eval (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression13_3.eval (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression13_4.eval (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression13_5.eval (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression13_6.eval (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression13_7.eval (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression13_8.eval (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5, same6, same7, same8]
  exact valid

theorem generic_lookup14
    (sourceValue : Fin 113 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BlakeGCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BlakeGCached.native.assigned (Airbender.Compiler.HelperValidityNative.BlakeGCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BlakeGCached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.genericExpressions14).Contains (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BlakeGCached.native.genericQueries.get ⟨14, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.BlakeGCached.native.genericQueries ⟨14, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BlakeGCached.native.field14_0.source ∈ Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields ⟨126, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeGCached.native.field14_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.generic_value14_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BlakeGCached.native.field14_1.source ∈ Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields ⟨127, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeGCached.native.field14_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.generic_value14_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BlakeGCached.native.field14_2.source ∈ Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields ⟨128, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeGCached.native.field14_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.generic_value14_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.BlakeGCached.native.field14_3.source ∈ Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields ⟨129, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeGCached.native.field14_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.generic_value14_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.BlakeGCached.native.field14_4.source ∈ Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields ⟨130, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeGCached.native.field14_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.generic_value14_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.BlakeGCached.native.field14_5.source ∈ Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields ⟨131, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeGCached.native.field14_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.generic_value14_5 physical data arithmetic).trans transported5
  have present6 : Airbender.Compiler.LookupNative.BlakeGCached.native.field14_6.source ∈ Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields ⟨132, by decide⟩
  have transported6 := Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeGCached.native.field14_6.source present6
  have same6 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.generic_value14_6 physical data arithmetic).trans transported6
  have present7 : Airbender.Compiler.LookupNative.BlakeGCached.native.field14_7.source ∈ Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields ⟨133, by decide⟩
  have transported7 := Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeGCached.native.field14_7.source present7
  have same7 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.generic_value14_7 physical data arithmetic).trans transported7
  have present8 : Airbender.Compiler.LookupNative.BlakeGCached.native.field14_8.source ∈ Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields ⟨134, by decide⟩
  have transported8 := Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeGCached.native.field14_8.source present8
  have same8 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.generic_value14_8 physical data arithmetic).trans transported8
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BlakeGCached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BlakeGCached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Blake2G" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.genericExpressions14, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BlakeGCached.native.model.Contains Airbender.Compiler.TableNative.BlakeGCached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression14_0.eval (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression14_1.eval (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression14_2.eval (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression14_3.eval (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression14_4.eval (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression14_5.eval (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression14_6.eval (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression14_7.eval (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression14_8.eval (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5, same6, same7, same8]
  exact valid

theorem generic_lookup15
    (sourceValue : Fin 113 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BlakeGCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BlakeGCached.native.assigned (Airbender.Compiler.HelperValidityNative.BlakeGCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BlakeGCached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.genericExpressions15).Contains (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BlakeGCached.native.genericQueries.get ⟨15, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.BlakeGCached.native.genericQueries ⟨15, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BlakeGCached.native.field15_0.source ∈ Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields ⟨135, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeGCached.native.field15_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.generic_value15_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BlakeGCached.native.field15_1.source ∈ Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields ⟨136, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeGCached.native.field15_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.generic_value15_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BlakeGCached.native.field15_2.source ∈ Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields ⟨137, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeGCached.native.field15_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.generic_value15_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.BlakeGCached.native.field15_3.source ∈ Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields ⟨138, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeGCached.native.field15_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.generic_value15_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.BlakeGCached.native.field15_4.source ∈ Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields ⟨139, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeGCached.native.field15_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.generic_value15_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.BlakeGCached.native.field15_5.source ∈ Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields ⟨140, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeGCached.native.field15_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.generic_value15_5 physical data arithmetic).trans transported5
  have present6 : Airbender.Compiler.LookupNative.BlakeGCached.native.field15_6.source ∈ Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields ⟨141, by decide⟩
  have transported6 := Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeGCached.native.field15_6.source present6
  have same6 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.generic_value15_6 physical data arithmetic).trans transported6
  have present7 : Airbender.Compiler.LookupNative.BlakeGCached.native.field15_7.source ∈ Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields ⟨142, by decide⟩
  have transported7 := Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeGCached.native.field15_7.source present7
  have same7 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.generic_value15_7 physical data arithmetic).trans transported7
  have present8 : Airbender.Compiler.LookupNative.BlakeGCached.native.field15_8.source ∈ Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields ⟨143, by decide⟩
  have transported8 := Airbender.Compiler.QueryFrameNative.BlakeGCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeGCached.native.field15_8.source present8
  have same8 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.generic_value15_8 physical data arithmetic).trans transported8
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BlakeGCached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BlakeGCached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Blake2G" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.genericExpressions15, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BlakeGCached.native.model.Contains Airbender.Compiler.TableNative.BlakeGCached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression15_0.eval (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression15_1.eval (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression15_2.eval (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression15_3.eval (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression15_4.eval (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression15_5.eval (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression15_6.eval (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression15_7.eval (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression15_8.eval (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5, same6, same7, same8]
  exact valid


end Airbender.Compiler.CleanClosedNative.BlakeGCached
