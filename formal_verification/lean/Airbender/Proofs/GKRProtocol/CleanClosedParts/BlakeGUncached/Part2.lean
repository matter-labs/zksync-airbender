import Airbender.Proofs.GKRProtocol.CleanClosedParts.BlakeGUncached.Shared

namespace Airbender.Compiler.CleanClosedNative.BlakeGUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

theorem generic_lookup16
    (sourceValue : Fin 112 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BlakeGUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BlakeGUncached.native.assigned (Airbender.Compiler.HelperValidityNative.BlakeGUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BlakeGUncached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BlakeGUncached.native.genericExpressions16).Contains (Airbender.Compiler.CleanArithmeticNative.BlakeGUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.genericQueries.get ⟨16, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.genericQueries ⟨16, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BlakeGUncached.native.field16_0.source ∈ Airbender.Compiler.QueryFrameNative.BlakeGUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeGUncached.native.fields ⟨144, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BlakeGUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeGUncached.native.field16_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeGUncached.native.part2.generic_value16_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BlakeGUncached.native.field16_1.source ∈ Airbender.Compiler.QueryFrameNative.BlakeGUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeGUncached.native.fields ⟨145, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BlakeGUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeGUncached.native.field16_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeGUncached.native.part2.generic_value16_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BlakeGUncached.native.field16_2.source ∈ Airbender.Compiler.QueryFrameNative.BlakeGUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeGUncached.native.fields ⟨146, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BlakeGUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeGUncached.native.field16_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeGUncached.native.part2.generic_value16_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.BlakeGUncached.native.field16_3.source ∈ Airbender.Compiler.QueryFrameNative.BlakeGUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeGUncached.native.fields ⟨147, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.BlakeGUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeGUncached.native.field16_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeGUncached.native.part2.generic_value16_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.BlakeGUncached.native.field16_4.source ∈ Airbender.Compiler.QueryFrameNative.BlakeGUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeGUncached.native.fields ⟨148, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.BlakeGUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeGUncached.native.field16_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeGUncached.native.part2.generic_value16_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.BlakeGUncached.native.field16_5.source ∈ Airbender.Compiler.QueryFrameNative.BlakeGUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeGUncached.native.fields ⟨149, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.BlakeGUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeGUncached.native.field16_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeGUncached.native.part2.generic_value16_5 physical data arithmetic).trans transported5
  have present6 : Airbender.Compiler.LookupNative.BlakeGUncached.native.field16_6.source ∈ Airbender.Compiler.QueryFrameNative.BlakeGUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeGUncached.native.fields ⟨150, by decide⟩
  have transported6 := Airbender.Compiler.QueryFrameNative.BlakeGUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeGUncached.native.field16_6.source present6
  have same6 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeGUncached.native.part2.generic_value16_6 physical data arithmetic).trans transported6
  have present7 : Airbender.Compiler.LookupNative.BlakeGUncached.native.field16_7.source ∈ Airbender.Compiler.QueryFrameNative.BlakeGUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeGUncached.native.fields ⟨151, by decide⟩
  have transported7 := Airbender.Compiler.QueryFrameNative.BlakeGUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeGUncached.native.field16_7.source present7
  have same7 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeGUncached.native.part2.generic_value16_7 physical data arithmetic).trans transported7
  have present8 : Airbender.Compiler.LookupNative.BlakeGUncached.native.field16_8.source ∈ Airbender.Compiler.QueryFrameNative.BlakeGUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeGUncached.native.fields ⟨152, by decide⟩
  have transported8 := Airbender.Compiler.QueryFrameNative.BlakeGUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeGUncached.native.field16_8.source present8
  have same8 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeGUncached.native.part2.generic_value16_8 physical data arithmetic).trans transported8
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BlakeGUncached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BlakeGUncached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Blake2G" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BlakeGUncached.native.genericExpressions16, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BlakeGUncached.native.model.Contains Airbender.Compiler.TableNative.BlakeGUncached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BlakeGUncached.native.part2.genericExpression16_0.eval (Airbender.Compiler.CleanArithmeticNative.BlakeGUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeGUncached.native.part2.genericExpression16_1.eval (Airbender.Compiler.CleanArithmeticNative.BlakeGUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeGUncached.native.part2.genericExpression16_2.eval (Airbender.Compiler.CleanArithmeticNative.BlakeGUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeGUncached.native.part2.genericExpression16_3.eval (Airbender.Compiler.CleanArithmeticNative.BlakeGUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeGUncached.native.part2.genericExpression16_4.eval (Airbender.Compiler.CleanArithmeticNative.BlakeGUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeGUncached.native.part2.genericExpression16_5.eval (Airbender.Compiler.CleanArithmeticNative.BlakeGUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeGUncached.native.part2.genericExpression16_6.eval (Airbender.Compiler.CleanArithmeticNative.BlakeGUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeGUncached.native.part2.genericExpression16_7.eval (Airbender.Compiler.CleanArithmeticNative.BlakeGUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeGUncached.native.part2.genericExpression16_8.eval (Airbender.Compiler.CleanArithmeticNative.BlakeGUncached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5, same6, same7, same8]
  exact valid

theorem generic_lookup17
    (sourceValue : Fin 112 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BlakeGUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BlakeGUncached.native.assigned (Airbender.Compiler.HelperValidityNative.BlakeGUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BlakeGUncached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BlakeGUncached.native.genericExpressions17).Contains (Airbender.Compiler.CleanArithmeticNative.BlakeGUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.genericQueries.get ⟨17, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.genericQueries ⟨17, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BlakeGUncached.native.field17_0.source ∈ Airbender.Compiler.QueryFrameNative.BlakeGUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeGUncached.native.fields ⟨153, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BlakeGUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeGUncached.native.field17_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeGUncached.native.part2.generic_value17_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BlakeGUncached.native.field17_1.source ∈ Airbender.Compiler.QueryFrameNative.BlakeGUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeGUncached.native.fields ⟨154, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BlakeGUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeGUncached.native.field17_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeGUncached.native.part2.generic_value17_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BlakeGUncached.native.field17_2.source ∈ Airbender.Compiler.QueryFrameNative.BlakeGUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeGUncached.native.fields ⟨155, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BlakeGUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeGUncached.native.field17_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeGUncached.native.part2.generic_value17_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.BlakeGUncached.native.field17_3.source ∈ Airbender.Compiler.QueryFrameNative.BlakeGUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeGUncached.native.fields ⟨156, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.BlakeGUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeGUncached.native.field17_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeGUncached.native.part2.generic_value17_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.BlakeGUncached.native.field17_4.source ∈ Airbender.Compiler.QueryFrameNative.BlakeGUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeGUncached.native.fields ⟨157, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.BlakeGUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeGUncached.native.field17_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeGUncached.native.part2.generic_value17_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.BlakeGUncached.native.field17_5.source ∈ Airbender.Compiler.QueryFrameNative.BlakeGUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeGUncached.native.fields ⟨158, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.BlakeGUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeGUncached.native.field17_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeGUncached.native.part2.generic_value17_5 physical data arithmetic).trans transported5
  have present6 : Airbender.Compiler.LookupNative.BlakeGUncached.native.field17_6.source ∈ Airbender.Compiler.QueryFrameNative.BlakeGUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeGUncached.native.fields ⟨159, by decide⟩
  have transported6 := Airbender.Compiler.QueryFrameNative.BlakeGUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeGUncached.native.field17_6.source present6
  have same6 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeGUncached.native.part2.generic_value17_6 physical data arithmetic).trans transported6
  have present7 : Airbender.Compiler.LookupNative.BlakeGUncached.native.field17_7.source ∈ Airbender.Compiler.QueryFrameNative.BlakeGUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeGUncached.native.fields ⟨160, by decide⟩
  have transported7 := Airbender.Compiler.QueryFrameNative.BlakeGUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeGUncached.native.field17_7.source present7
  have same7 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeGUncached.native.part2.generic_value17_7 physical data arithmetic).trans transported7
  have present8 : Airbender.Compiler.LookupNative.BlakeGUncached.native.field17_8.source ∈ Airbender.Compiler.QueryFrameNative.BlakeGUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeGUncached.native.fields ⟨161, by decide⟩
  have transported8 := Airbender.Compiler.QueryFrameNative.BlakeGUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeGUncached.native.field17_8.source present8
  have same8 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeGUncached.native.part2.generic_value17_8 physical data arithmetic).trans transported8
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BlakeGUncached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BlakeGUncached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Blake2G" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BlakeGUncached.native.genericExpressions17, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BlakeGUncached.native.model.Contains Airbender.Compiler.TableNative.BlakeGUncached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BlakeGUncached.native.part2.genericExpression17_0.eval (Airbender.Compiler.CleanArithmeticNative.BlakeGUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeGUncached.native.part2.genericExpression17_1.eval (Airbender.Compiler.CleanArithmeticNative.BlakeGUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeGUncached.native.part2.genericExpression17_2.eval (Airbender.Compiler.CleanArithmeticNative.BlakeGUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeGUncached.native.part2.genericExpression17_3.eval (Airbender.Compiler.CleanArithmeticNative.BlakeGUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeGUncached.native.part2.genericExpression17_4.eval (Airbender.Compiler.CleanArithmeticNative.BlakeGUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeGUncached.native.part2.genericExpression17_5.eval (Airbender.Compiler.CleanArithmeticNative.BlakeGUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeGUncached.native.part2.genericExpression17_6.eval (Airbender.Compiler.CleanArithmeticNative.BlakeGUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeGUncached.native.part2.genericExpression17_7.eval (Airbender.Compiler.CleanArithmeticNative.BlakeGUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeGUncached.native.part2.genericExpression17_8.eval (Airbender.Compiler.CleanArithmeticNative.BlakeGUncached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5, same6, same7, same8]
  exact valid

theorem generic_lookup18
    (sourceValue : Fin 112 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BlakeGUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BlakeGUncached.native.assigned (Airbender.Compiler.HelperValidityNative.BlakeGUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BlakeGUncached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BlakeGUncached.native.genericExpressions18).Contains (Airbender.Compiler.CleanArithmeticNative.BlakeGUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.genericQueries.get ⟨18, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.genericQueries ⟨18, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BlakeGUncached.native.field18_0.source ∈ Airbender.Compiler.QueryFrameNative.BlakeGUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeGUncached.native.fields ⟨162, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BlakeGUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeGUncached.native.field18_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeGUncached.native.part2.generic_value18_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BlakeGUncached.native.field18_1.source ∈ Airbender.Compiler.QueryFrameNative.BlakeGUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeGUncached.native.fields ⟨163, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BlakeGUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeGUncached.native.field18_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeGUncached.native.part2.generic_value18_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BlakeGUncached.native.field18_2.source ∈ Airbender.Compiler.QueryFrameNative.BlakeGUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeGUncached.native.fields ⟨164, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BlakeGUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeGUncached.native.field18_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeGUncached.native.part2.generic_value18_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.BlakeGUncached.native.field18_3.source ∈ Airbender.Compiler.QueryFrameNative.BlakeGUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeGUncached.native.fields ⟨165, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.BlakeGUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeGUncached.native.field18_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeGUncached.native.part2.generic_value18_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.BlakeGUncached.native.field18_4.source ∈ Airbender.Compiler.QueryFrameNative.BlakeGUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeGUncached.native.fields ⟨166, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.BlakeGUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeGUncached.native.field18_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeGUncached.native.part2.generic_value18_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.BlakeGUncached.native.field18_5.source ∈ Airbender.Compiler.QueryFrameNative.BlakeGUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeGUncached.native.fields ⟨167, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.BlakeGUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeGUncached.native.field18_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeGUncached.native.part2.generic_value18_5 physical data arithmetic).trans transported5
  have present6 : Airbender.Compiler.LookupNative.BlakeGUncached.native.field18_6.source ∈ Airbender.Compiler.QueryFrameNative.BlakeGUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeGUncached.native.fields ⟨168, by decide⟩
  have transported6 := Airbender.Compiler.QueryFrameNative.BlakeGUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeGUncached.native.field18_6.source present6
  have same6 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeGUncached.native.part2.generic_value18_6 physical data arithmetic).trans transported6
  have present7 : Airbender.Compiler.LookupNative.BlakeGUncached.native.field18_7.source ∈ Airbender.Compiler.QueryFrameNative.BlakeGUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeGUncached.native.fields ⟨169, by decide⟩
  have transported7 := Airbender.Compiler.QueryFrameNative.BlakeGUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeGUncached.native.field18_7.source present7
  have same7 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeGUncached.native.part2.generic_value18_7 physical data arithmetic).trans transported7
  have present8 : Airbender.Compiler.LookupNative.BlakeGUncached.native.field18_8.source ∈ Airbender.Compiler.QueryFrameNative.BlakeGUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeGUncached.native.fields ⟨170, by decide⟩
  have transported8 := Airbender.Compiler.QueryFrameNative.BlakeGUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeGUncached.native.field18_8.source present8
  have same8 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeGUncached.native.part2.generic_value18_8 physical data arithmetic).trans transported8
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BlakeGUncached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BlakeGUncached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Blake2G" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BlakeGUncached.native.genericExpressions18, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BlakeGUncached.native.model.Contains Airbender.Compiler.TableNative.BlakeGUncached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BlakeGUncached.native.part2.genericExpression18_0.eval (Airbender.Compiler.CleanArithmeticNative.BlakeGUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeGUncached.native.part2.genericExpression18_1.eval (Airbender.Compiler.CleanArithmeticNative.BlakeGUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeGUncached.native.part2.genericExpression18_2.eval (Airbender.Compiler.CleanArithmeticNative.BlakeGUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeGUncached.native.part2.genericExpression18_3.eval (Airbender.Compiler.CleanArithmeticNative.BlakeGUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeGUncached.native.part2.genericExpression18_4.eval (Airbender.Compiler.CleanArithmeticNative.BlakeGUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeGUncached.native.part2.genericExpression18_5.eval (Airbender.Compiler.CleanArithmeticNative.BlakeGUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeGUncached.native.part2.genericExpression18_6.eval (Airbender.Compiler.CleanArithmeticNative.BlakeGUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeGUncached.native.part2.genericExpression18_7.eval (Airbender.Compiler.CleanArithmeticNative.BlakeGUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeGUncached.native.part2.genericExpression18_8.eval (Airbender.Compiler.CleanArithmeticNative.BlakeGUncached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5, same6, same7, same8]
  exact valid


end Airbender.Compiler.CleanClosedNative.BlakeGUncached
