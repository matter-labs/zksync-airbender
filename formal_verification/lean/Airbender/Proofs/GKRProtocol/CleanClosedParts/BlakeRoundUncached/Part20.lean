import Airbender.Proofs.GKRProtocol.CleanClosedParts.BlakeRoundUncached.Shared

namespace Airbender.Compiler.CleanClosedNative.BlakeRoundUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

theorem generic_lookup160
    (sourceValue : Fin 763 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BlakeRoundUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BlakeRoundUncached.native.assigned (Airbender.Compiler.HelperValidityNative.BlakeRoundUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BlakeRoundUncached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.genericExpressions160).Contains (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.genericQueries.get ⟨160, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.genericQueries ⟨160, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field160_0.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨960, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field160_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part20.generic_value160_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field160_1.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨961, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field160_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part20.generic_value160_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field160_2.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨962, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field160_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part20.generic_value160_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field160_3.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨963, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field160_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part20.generic_value160_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field160_4.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨964, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field160_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part20.generic_value160_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field160_5.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨965, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field160_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part20.generic_value160_5 physical data arithmetic).trans transported5
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BlakeRoundUncached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BlakeRoundUncached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Blake2Round" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.genericExpressions160, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BlakeRoundUncached.native.model.Contains Airbender.Compiler.TableNative.BlakeRoundUncached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part20.genericExpression160_0.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part20.genericExpression160_1.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part20.genericExpression160_2.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part20.genericExpression160_3.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part20.genericExpression160_4.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part20.genericExpression160_5.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5]
  exact valid

theorem generic_lookup161
    (sourceValue : Fin 763 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BlakeRoundUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BlakeRoundUncached.native.assigned (Airbender.Compiler.HelperValidityNative.BlakeRoundUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BlakeRoundUncached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.genericExpressions161).Contains (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.genericQueries.get ⟨161, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.genericQueries ⟨161, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field161_0.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨966, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field161_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part20.generic_value161_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field161_1.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨967, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field161_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part20.generic_value161_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field161_2.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨968, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field161_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part20.generic_value161_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field161_3.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨969, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field161_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part20.generic_value161_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field161_4.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨970, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field161_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part20.generic_value161_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field161_5.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨971, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field161_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part20.generic_value161_5 physical data arithmetic).trans transported5
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BlakeRoundUncached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BlakeRoundUncached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Blake2Round" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.genericExpressions161, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BlakeRoundUncached.native.model.Contains Airbender.Compiler.TableNative.BlakeRoundUncached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part20.genericExpression161_0.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part20.genericExpression161_1.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part20.genericExpression161_2.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part20.genericExpression161_3.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part20.genericExpression161_4.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part20.genericExpression161_5.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5]
  exact valid

theorem generic_lookup162
    (sourceValue : Fin 763 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BlakeRoundUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BlakeRoundUncached.native.assigned (Airbender.Compiler.HelperValidityNative.BlakeRoundUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BlakeRoundUncached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.genericExpressions162).Contains (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.genericQueries.get ⟨162, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.genericQueries ⟨162, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field162_0.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨972, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field162_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part20.generic_value162_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field162_1.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨973, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field162_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part20.generic_value162_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field162_2.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨974, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field162_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part20.generic_value162_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field162_3.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨975, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field162_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part20.generic_value162_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field162_4.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨976, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field162_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part20.generic_value162_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field162_5.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨977, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field162_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part20.generic_value162_5 physical data arithmetic).trans transported5
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BlakeRoundUncached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BlakeRoundUncached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Blake2Round" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.genericExpressions162, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BlakeRoundUncached.native.model.Contains Airbender.Compiler.TableNative.BlakeRoundUncached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part20.genericExpression162_0.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part20.genericExpression162_1.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part20.genericExpression162_2.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part20.genericExpression162_3.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part20.genericExpression162_4.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part20.genericExpression162_5.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5]
  exact valid

theorem generic_lookup163
    (sourceValue : Fin 763 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BlakeRoundUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BlakeRoundUncached.native.assigned (Airbender.Compiler.HelperValidityNative.BlakeRoundUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BlakeRoundUncached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.genericExpressions163).Contains (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.genericQueries.get ⟨163, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.genericQueries ⟨163, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field163_0.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨978, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field163_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part20.generic_value163_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field163_1.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨979, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field163_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part20.generic_value163_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field163_2.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨980, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field163_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part20.generic_value163_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field163_3.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨981, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field163_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part20.generic_value163_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field163_4.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨982, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field163_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part20.generic_value163_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field163_5.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨983, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field163_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part20.generic_value163_5 physical data arithmetic).trans transported5
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BlakeRoundUncached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BlakeRoundUncached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Blake2Round" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.genericExpressions163, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BlakeRoundUncached.native.model.Contains Airbender.Compiler.TableNative.BlakeRoundUncached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part20.genericExpression163_0.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part20.genericExpression163_1.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part20.genericExpression163_2.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part20.genericExpression163_3.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part20.genericExpression163_4.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part20.genericExpression163_5.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5]
  exact valid

theorem generic_lookup164
    (sourceValue : Fin 763 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BlakeRoundUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BlakeRoundUncached.native.assigned (Airbender.Compiler.HelperValidityNative.BlakeRoundUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BlakeRoundUncached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.genericExpressions164).Contains (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.genericQueries.get ⟨164, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.genericQueries ⟨164, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field164_0.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨984, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field164_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part20.generic_value164_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field164_1.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨985, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field164_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part20.generic_value164_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field164_2.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨986, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field164_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part20.generic_value164_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field164_3.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨987, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field164_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part20.generic_value164_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field164_4.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨988, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field164_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part20.generic_value164_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field164_5.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨989, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field164_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part20.generic_value164_5 physical data arithmetic).trans transported5
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BlakeRoundUncached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BlakeRoundUncached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Blake2Round" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.genericExpressions164, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BlakeRoundUncached.native.model.Contains Airbender.Compiler.TableNative.BlakeRoundUncached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part20.genericExpression164_0.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part20.genericExpression164_1.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part20.genericExpression164_2.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part20.genericExpression164_3.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part20.genericExpression164_4.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part20.genericExpression164_5.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5]
  exact valid

theorem generic_lookup165
    (sourceValue : Fin 763 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BlakeRoundUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BlakeRoundUncached.native.assigned (Airbender.Compiler.HelperValidityNative.BlakeRoundUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BlakeRoundUncached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.genericExpressions165).Contains (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.genericQueries.get ⟨165, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.genericQueries ⟨165, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field165_0.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨990, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field165_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part20.generic_value165_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field165_1.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨991, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field165_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part20.generic_value165_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field165_2.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨992, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field165_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part20.generic_value165_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field165_3.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨993, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field165_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part20.generic_value165_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field165_4.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨994, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field165_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part20.generic_value165_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field165_5.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨995, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field165_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part20.generic_value165_5 physical data arithmetic).trans transported5
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BlakeRoundUncached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BlakeRoundUncached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Blake2Round" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.genericExpressions165, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BlakeRoundUncached.native.model.Contains Airbender.Compiler.TableNative.BlakeRoundUncached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part20.genericExpression165_0.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part20.genericExpression165_1.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part20.genericExpression165_2.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part20.genericExpression165_3.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part20.genericExpression165_4.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part20.genericExpression165_5.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5]
  exact valid

theorem generic_lookup166
    (sourceValue : Fin 763 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BlakeRoundUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BlakeRoundUncached.native.assigned (Airbender.Compiler.HelperValidityNative.BlakeRoundUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BlakeRoundUncached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.genericExpressions166).Contains (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.genericQueries.get ⟨166, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.genericQueries ⟨166, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field166_0.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨996, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field166_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part20.generic_value166_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field166_1.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨997, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field166_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part20.generic_value166_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field166_2.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨998, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field166_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part20.generic_value166_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field166_3.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨999, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field166_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part20.generic_value166_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field166_4.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨1000, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field166_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part20.generic_value166_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field166_5.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨1001, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field166_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part20.generic_value166_5 physical data arithmetic).trans transported5
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BlakeRoundUncached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BlakeRoundUncached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Blake2Round" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.genericExpressions166, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BlakeRoundUncached.native.model.Contains Airbender.Compiler.TableNative.BlakeRoundUncached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part20.genericExpression166_0.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part20.genericExpression166_1.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part20.genericExpression166_2.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part20.genericExpression166_3.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part20.genericExpression166_4.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part20.genericExpression166_5.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5]
  exact valid

theorem generic_lookup167
    (sourceValue : Fin 763 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BlakeRoundUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BlakeRoundUncached.native.assigned (Airbender.Compiler.HelperValidityNative.BlakeRoundUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BlakeRoundUncached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.genericExpressions167).Contains (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.genericQueries.get ⟨167, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.genericQueries ⟨167, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field167_0.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨1002, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field167_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part20.generic_value167_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field167_1.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨1003, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field167_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part20.generic_value167_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field167_2.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨1004, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field167_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part20.generic_value167_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field167_3.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨1005, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field167_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part20.generic_value167_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field167_4.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨1006, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field167_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part20.generic_value167_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field167_5.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨1007, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field167_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part20.generic_value167_5 physical data arithmetic).trans transported5
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BlakeRoundUncached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BlakeRoundUncached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Blake2Round" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.genericExpressions167, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BlakeRoundUncached.native.model.Contains Airbender.Compiler.TableNative.BlakeRoundUncached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part20.genericExpression167_0.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part20.genericExpression167_1.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part20.genericExpression167_2.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part20.genericExpression167_3.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part20.genericExpression167_4.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part20.genericExpression167_5.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5]
  exact valid


end Airbender.Compiler.CleanClosedNative.BlakeRoundUncached
