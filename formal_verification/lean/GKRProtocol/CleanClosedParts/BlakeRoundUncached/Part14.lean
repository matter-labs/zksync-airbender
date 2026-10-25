import GKRProtocol.CleanClosedParts.BlakeRoundUncached.Shared

namespace Airbender.Compiler.CleanClosedNative.BlakeRoundUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

theorem generic_lookup112
    (sourceValue : Fin 763 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BlakeRoundUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BlakeRoundUncached.native.assigned (Airbender.Compiler.HelperValidityNative.BlakeRoundUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BlakeRoundUncached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.genericExpressions112).Contains (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.genericQueries.get ⟨112, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.genericQueries ⟨112, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field112_0.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨672, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field112_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part14.generic_value112_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field112_1.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨673, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field112_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part14.generic_value112_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field112_2.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨674, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field112_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part14.generic_value112_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field112_3.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨675, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field112_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part14.generic_value112_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field112_4.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨676, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field112_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part14.generic_value112_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field112_5.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨677, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field112_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part14.generic_value112_5 physical data arithmetic).trans transported5
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BlakeRoundUncached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BlakeRoundUncached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Blake2Round" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.genericExpressions112, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BlakeRoundUncached.native.model.Contains Airbender.Compiler.TableNative.BlakeRoundUncached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part14.genericExpression112_0.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part14.genericExpression112_1.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part14.genericExpression112_2.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part14.genericExpression112_3.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part14.genericExpression112_4.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part14.genericExpression112_5.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5]
  exact valid

theorem generic_lookup113
    (sourceValue : Fin 763 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BlakeRoundUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BlakeRoundUncached.native.assigned (Airbender.Compiler.HelperValidityNative.BlakeRoundUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BlakeRoundUncached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.genericExpressions113).Contains (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.genericQueries.get ⟨113, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.genericQueries ⟨113, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field113_0.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨678, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field113_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part14.generic_value113_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field113_1.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨679, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field113_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part14.generic_value113_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field113_2.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨680, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field113_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part14.generic_value113_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field113_3.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨681, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field113_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part14.generic_value113_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field113_4.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨682, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field113_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part14.generic_value113_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field113_5.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨683, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field113_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part14.generic_value113_5 physical data arithmetic).trans transported5
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BlakeRoundUncached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BlakeRoundUncached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Blake2Round" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.genericExpressions113, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BlakeRoundUncached.native.model.Contains Airbender.Compiler.TableNative.BlakeRoundUncached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part14.genericExpression113_0.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part14.genericExpression113_1.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part14.genericExpression113_2.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part14.genericExpression113_3.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part14.genericExpression113_4.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part14.genericExpression113_5.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5]
  exact valid

theorem generic_lookup114
    (sourceValue : Fin 763 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BlakeRoundUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BlakeRoundUncached.native.assigned (Airbender.Compiler.HelperValidityNative.BlakeRoundUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BlakeRoundUncached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.genericExpressions114).Contains (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.genericQueries.get ⟨114, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.genericQueries ⟨114, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field114_0.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨684, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field114_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part14.generic_value114_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field114_1.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨685, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field114_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part14.generic_value114_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field114_2.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨686, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field114_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part14.generic_value114_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field114_3.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨687, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field114_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part14.generic_value114_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field114_4.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨688, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field114_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part14.generic_value114_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field114_5.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨689, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field114_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part14.generic_value114_5 physical data arithmetic).trans transported5
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BlakeRoundUncached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BlakeRoundUncached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Blake2Round" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.genericExpressions114, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BlakeRoundUncached.native.model.Contains Airbender.Compiler.TableNative.BlakeRoundUncached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part14.genericExpression114_0.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part14.genericExpression114_1.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part14.genericExpression114_2.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part14.genericExpression114_3.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part14.genericExpression114_4.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part14.genericExpression114_5.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5]
  exact valid

theorem generic_lookup115
    (sourceValue : Fin 763 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BlakeRoundUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BlakeRoundUncached.native.assigned (Airbender.Compiler.HelperValidityNative.BlakeRoundUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BlakeRoundUncached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.genericExpressions115).Contains (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.genericQueries.get ⟨115, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.genericQueries ⟨115, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field115_0.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨690, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field115_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part14.generic_value115_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field115_1.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨691, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field115_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part14.generic_value115_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field115_2.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨692, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field115_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part14.generic_value115_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field115_3.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨693, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field115_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part14.generic_value115_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field115_4.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨694, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field115_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part14.generic_value115_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field115_5.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨695, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field115_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part14.generic_value115_5 physical data arithmetic).trans transported5
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BlakeRoundUncached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BlakeRoundUncached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Blake2Round" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.genericExpressions115, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BlakeRoundUncached.native.model.Contains Airbender.Compiler.TableNative.BlakeRoundUncached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part14.genericExpression115_0.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part14.genericExpression115_1.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part14.genericExpression115_2.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part14.genericExpression115_3.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part14.genericExpression115_4.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part14.genericExpression115_5.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5]
  exact valid

theorem generic_lookup116
    (sourceValue : Fin 763 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BlakeRoundUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BlakeRoundUncached.native.assigned (Airbender.Compiler.HelperValidityNative.BlakeRoundUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BlakeRoundUncached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.genericExpressions116).Contains (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.genericQueries.get ⟨116, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.genericQueries ⟨116, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field116_0.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨696, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field116_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part14.generic_value116_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field116_1.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨697, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field116_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part14.generic_value116_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field116_2.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨698, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field116_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part14.generic_value116_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field116_3.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨699, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field116_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part14.generic_value116_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field116_4.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨700, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field116_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part14.generic_value116_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field116_5.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨701, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field116_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part14.generic_value116_5 physical data arithmetic).trans transported5
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BlakeRoundUncached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BlakeRoundUncached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Blake2Round" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.genericExpressions116, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BlakeRoundUncached.native.model.Contains Airbender.Compiler.TableNative.BlakeRoundUncached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part14.genericExpression116_0.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part14.genericExpression116_1.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part14.genericExpression116_2.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part14.genericExpression116_3.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part14.genericExpression116_4.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part14.genericExpression116_5.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5]
  exact valid

theorem generic_lookup117
    (sourceValue : Fin 763 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BlakeRoundUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BlakeRoundUncached.native.assigned (Airbender.Compiler.HelperValidityNative.BlakeRoundUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BlakeRoundUncached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.genericExpressions117).Contains (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.genericQueries.get ⟨117, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.genericQueries ⟨117, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field117_0.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨702, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field117_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part14.generic_value117_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field117_1.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨703, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field117_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part14.generic_value117_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field117_2.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨704, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field117_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part14.generic_value117_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field117_3.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨705, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field117_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part14.generic_value117_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field117_4.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨706, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field117_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part14.generic_value117_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field117_5.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨707, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field117_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part14.generic_value117_5 physical data arithmetic).trans transported5
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BlakeRoundUncached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BlakeRoundUncached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Blake2Round" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.genericExpressions117, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BlakeRoundUncached.native.model.Contains Airbender.Compiler.TableNative.BlakeRoundUncached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part14.genericExpression117_0.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part14.genericExpression117_1.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part14.genericExpression117_2.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part14.genericExpression117_3.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part14.genericExpression117_4.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part14.genericExpression117_5.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5]
  exact valid

theorem generic_lookup118
    (sourceValue : Fin 763 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BlakeRoundUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BlakeRoundUncached.native.assigned (Airbender.Compiler.HelperValidityNative.BlakeRoundUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BlakeRoundUncached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.genericExpressions118).Contains (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.genericQueries.get ⟨118, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.genericQueries ⟨118, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field118_0.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨708, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field118_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part14.generic_value118_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field118_1.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨709, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field118_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part14.generic_value118_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field118_2.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨710, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field118_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part14.generic_value118_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field118_3.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨711, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field118_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part14.generic_value118_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field118_4.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨712, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field118_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part14.generic_value118_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field118_5.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨713, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field118_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part14.generic_value118_5 physical data arithmetic).trans transported5
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BlakeRoundUncached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BlakeRoundUncached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Blake2Round" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.genericExpressions118, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BlakeRoundUncached.native.model.Contains Airbender.Compiler.TableNative.BlakeRoundUncached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part14.genericExpression118_0.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part14.genericExpression118_1.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part14.genericExpression118_2.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part14.genericExpression118_3.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part14.genericExpression118_4.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part14.genericExpression118_5.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5]
  exact valid

theorem generic_lookup119
    (sourceValue : Fin 763 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BlakeRoundUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BlakeRoundUncached.native.assigned (Airbender.Compiler.HelperValidityNative.BlakeRoundUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BlakeRoundUncached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.genericExpressions119).Contains (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.genericQueries.get ⟨119, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.genericQueries ⟨119, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field119_0.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨714, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field119_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part14.generic_value119_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field119_1.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨715, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field119_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part14.generic_value119_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field119_2.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨716, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field119_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part14.generic_value119_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field119_3.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨717, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field119_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part14.generic_value119_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field119_4.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨718, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field119_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part14.generic_value119_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field119_5.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨719, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field119_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part14.generic_value119_5 physical data arithmetic).trans transported5
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BlakeRoundUncached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BlakeRoundUncached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Blake2Round" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.genericExpressions119, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BlakeRoundUncached.native.model.Contains Airbender.Compiler.TableNative.BlakeRoundUncached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part14.genericExpression119_0.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part14.genericExpression119_1.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part14.genericExpression119_2.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part14.genericExpression119_3.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part14.genericExpression119_4.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part14.genericExpression119_5.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5]
  exact valid


end Airbender.Compiler.CleanClosedNative.BlakeRoundUncached
