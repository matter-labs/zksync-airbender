import Airbender.Proofs.GKRProtocol.CleanClosedParts.BlakeRoundUncached.Shared

namespace Airbender.Compiler.CleanClosedNative.BlakeRoundUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

theorem generic_lookup56
    (sourceValue : Fin 763 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BlakeRoundUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BlakeRoundUncached.native.assigned (Airbender.Compiler.HelperValidityNative.BlakeRoundUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BlakeRoundUncached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.genericExpressions56).Contains (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.genericQueries.get ⟨56, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.genericQueries ⟨56, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field56_0.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨336, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field56_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part7.generic_value56_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field56_1.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨337, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field56_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part7.generic_value56_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field56_2.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨338, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field56_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part7.generic_value56_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field56_3.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨339, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field56_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part7.generic_value56_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field56_4.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨340, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field56_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part7.generic_value56_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field56_5.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨341, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field56_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part7.generic_value56_5 physical data arithmetic).trans transported5
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BlakeRoundUncached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BlakeRoundUncached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Blake2Round" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.genericExpressions56, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BlakeRoundUncached.native.model.Contains Airbender.Compiler.TableNative.BlakeRoundUncached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part7.genericExpression56_0.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part7.genericExpression56_1.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part7.genericExpression56_2.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part7.genericExpression56_3.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part7.genericExpression56_4.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part7.genericExpression56_5.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5]
  exact valid

theorem generic_lookup57
    (sourceValue : Fin 763 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BlakeRoundUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BlakeRoundUncached.native.assigned (Airbender.Compiler.HelperValidityNative.BlakeRoundUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BlakeRoundUncached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.genericExpressions57).Contains (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.genericQueries.get ⟨57, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.genericQueries ⟨57, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field57_0.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨342, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field57_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part7.generic_value57_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field57_1.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨343, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field57_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part7.generic_value57_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field57_2.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨344, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field57_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part7.generic_value57_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field57_3.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨345, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field57_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part7.generic_value57_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field57_4.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨346, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field57_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part7.generic_value57_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field57_5.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨347, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field57_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part7.generic_value57_5 physical data arithmetic).trans transported5
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BlakeRoundUncached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BlakeRoundUncached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Blake2Round" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.genericExpressions57, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BlakeRoundUncached.native.model.Contains Airbender.Compiler.TableNative.BlakeRoundUncached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part7.genericExpression57_0.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part7.genericExpression57_1.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part7.genericExpression57_2.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part7.genericExpression57_3.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part7.genericExpression57_4.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part7.genericExpression57_5.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5]
  exact valid

theorem generic_lookup58
    (sourceValue : Fin 763 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BlakeRoundUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BlakeRoundUncached.native.assigned (Airbender.Compiler.HelperValidityNative.BlakeRoundUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BlakeRoundUncached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.genericExpressions58).Contains (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.genericQueries.get ⟨58, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.genericQueries ⟨58, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field58_0.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨348, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field58_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part7.generic_value58_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field58_1.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨349, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field58_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part7.generic_value58_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field58_2.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨350, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field58_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part7.generic_value58_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field58_3.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨351, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field58_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part7.generic_value58_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field58_4.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨352, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field58_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part7.generic_value58_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field58_5.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨353, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field58_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part7.generic_value58_5 physical data arithmetic).trans transported5
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BlakeRoundUncached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BlakeRoundUncached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Blake2Round" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.genericExpressions58, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BlakeRoundUncached.native.model.Contains Airbender.Compiler.TableNative.BlakeRoundUncached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part7.genericExpression58_0.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part7.genericExpression58_1.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part7.genericExpression58_2.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part7.genericExpression58_3.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part7.genericExpression58_4.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part7.genericExpression58_5.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5]
  exact valid

theorem generic_lookup59
    (sourceValue : Fin 763 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BlakeRoundUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BlakeRoundUncached.native.assigned (Airbender.Compiler.HelperValidityNative.BlakeRoundUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BlakeRoundUncached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.genericExpressions59).Contains (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.genericQueries.get ⟨59, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.genericQueries ⟨59, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field59_0.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨354, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field59_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part7.generic_value59_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field59_1.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨355, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field59_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part7.generic_value59_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field59_2.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨356, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field59_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part7.generic_value59_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field59_3.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨357, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field59_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part7.generic_value59_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field59_4.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨358, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field59_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part7.generic_value59_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field59_5.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨359, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field59_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part7.generic_value59_5 physical data arithmetic).trans transported5
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BlakeRoundUncached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BlakeRoundUncached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Blake2Round" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.genericExpressions59, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BlakeRoundUncached.native.model.Contains Airbender.Compiler.TableNative.BlakeRoundUncached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part7.genericExpression59_0.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part7.genericExpression59_1.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part7.genericExpression59_2.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part7.genericExpression59_3.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part7.genericExpression59_4.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part7.genericExpression59_5.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5]
  exact valid

theorem generic_lookup60
    (sourceValue : Fin 763 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BlakeRoundUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BlakeRoundUncached.native.assigned (Airbender.Compiler.HelperValidityNative.BlakeRoundUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BlakeRoundUncached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.genericExpressions60).Contains (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.genericQueries.get ⟨60, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.genericQueries ⟨60, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field60_0.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨360, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field60_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part7.generic_value60_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field60_1.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨361, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field60_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part7.generic_value60_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field60_2.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨362, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field60_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part7.generic_value60_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field60_3.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨363, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field60_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part7.generic_value60_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field60_4.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨364, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field60_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part7.generic_value60_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field60_5.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨365, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field60_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part7.generic_value60_5 physical data arithmetic).trans transported5
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BlakeRoundUncached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BlakeRoundUncached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Blake2Round" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.genericExpressions60, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BlakeRoundUncached.native.model.Contains Airbender.Compiler.TableNative.BlakeRoundUncached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part7.genericExpression60_0.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part7.genericExpression60_1.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part7.genericExpression60_2.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part7.genericExpression60_3.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part7.genericExpression60_4.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part7.genericExpression60_5.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5]
  exact valid

theorem generic_lookup61
    (sourceValue : Fin 763 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BlakeRoundUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BlakeRoundUncached.native.assigned (Airbender.Compiler.HelperValidityNative.BlakeRoundUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BlakeRoundUncached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.genericExpressions61).Contains (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.genericQueries.get ⟨61, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.genericQueries ⟨61, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field61_0.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨366, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field61_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part7.generic_value61_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field61_1.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨367, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field61_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part7.generic_value61_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field61_2.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨368, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field61_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part7.generic_value61_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field61_3.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨369, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field61_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part7.generic_value61_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field61_4.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨370, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field61_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part7.generic_value61_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field61_5.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨371, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field61_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part7.generic_value61_5 physical data arithmetic).trans transported5
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BlakeRoundUncached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BlakeRoundUncached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Blake2Round" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.genericExpressions61, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BlakeRoundUncached.native.model.Contains Airbender.Compiler.TableNative.BlakeRoundUncached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part7.genericExpression61_0.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part7.genericExpression61_1.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part7.genericExpression61_2.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part7.genericExpression61_3.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part7.genericExpression61_4.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part7.genericExpression61_5.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5]
  exact valid

theorem generic_lookup62
    (sourceValue : Fin 763 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BlakeRoundUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BlakeRoundUncached.native.assigned (Airbender.Compiler.HelperValidityNative.BlakeRoundUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BlakeRoundUncached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.genericExpressions62).Contains (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.genericQueries.get ⟨62, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.genericQueries ⟨62, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field62_0.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨372, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field62_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part7.generic_value62_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field62_1.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨373, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field62_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part7.generic_value62_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field62_2.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨374, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field62_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part7.generic_value62_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field62_3.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨375, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field62_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part7.generic_value62_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field62_4.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨376, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field62_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part7.generic_value62_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field62_5.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨377, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field62_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part7.generic_value62_5 physical data arithmetic).trans transported5
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BlakeRoundUncached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BlakeRoundUncached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Blake2Round" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.genericExpressions62, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BlakeRoundUncached.native.model.Contains Airbender.Compiler.TableNative.BlakeRoundUncached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part7.genericExpression62_0.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part7.genericExpression62_1.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part7.genericExpression62_2.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part7.genericExpression62_3.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part7.genericExpression62_4.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part7.genericExpression62_5.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5]
  exact valid

theorem generic_lookup63
    (sourceValue : Fin 763 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BlakeRoundUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BlakeRoundUncached.native.assigned (Airbender.Compiler.HelperValidityNative.BlakeRoundUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BlakeRoundUncached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.genericExpressions63).Contains (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.genericQueries.get ⟨63, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.genericQueries ⟨63, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field63_0.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨378, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field63_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part7.generic_value63_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field63_1.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨379, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field63_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part7.generic_value63_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field63_2.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨380, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field63_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part7.generic_value63_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field63_3.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨381, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field63_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part7.generic_value63_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field63_4.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨382, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field63_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part7.generic_value63_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field63_5.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨383, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field63_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part7.generic_value63_5 physical data arithmetic).trans transported5
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BlakeRoundUncached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BlakeRoundUncached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Blake2Round" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.genericExpressions63, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BlakeRoundUncached.native.model.Contains Airbender.Compiler.TableNative.BlakeRoundUncached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part7.genericExpression63_0.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part7.genericExpression63_1.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part7.genericExpression63_2.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part7.genericExpression63_3.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part7.genericExpression63_4.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part7.genericExpression63_5.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5]
  exact valid


end Airbender.Compiler.CleanClosedNative.BlakeRoundUncached
