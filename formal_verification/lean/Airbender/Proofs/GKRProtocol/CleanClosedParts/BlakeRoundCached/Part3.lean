import Airbender.Proofs.GKRProtocol.CleanClosedParts.BlakeRoundCached.Shared

namespace Airbender.Compiler.CleanClosedNative.BlakeRoundCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

theorem generic_lookup24
    (sourceValue : Fin 763 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BlakeRoundCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BlakeRoundCached.native.assigned (Airbender.Compiler.HelperValidityNative.BlakeRoundCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BlakeRoundCached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.genericExpressions24).Contains (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BlakeRoundCached.native.genericQueries.get ⟨24, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.BlakeRoundCached.native.genericQueries ⟨24, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field24_0.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨144, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field24_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part3.generic_value24_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field24_1.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨145, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field24_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part3.generic_value24_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field24_2.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨146, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field24_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part3.generic_value24_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field24_3.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨147, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field24_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part3.generic_value24_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field24_4.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨148, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field24_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part3.generic_value24_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field24_5.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨149, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field24_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part3.generic_value24_5 physical data arithmetic).trans transported5
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BlakeRoundCached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BlakeRoundCached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Blake2Round" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.genericExpressions24, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BlakeRoundCached.native.model.Contains Airbender.Compiler.TableNative.BlakeRoundCached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part3.genericExpression24_0.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part3.genericExpression24_1.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part3.genericExpression24_2.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part3.genericExpression24_3.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part3.genericExpression24_4.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part3.genericExpression24_5.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5]
  exact valid

theorem generic_lookup25
    (sourceValue : Fin 763 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BlakeRoundCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BlakeRoundCached.native.assigned (Airbender.Compiler.HelperValidityNative.BlakeRoundCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BlakeRoundCached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.genericExpressions25).Contains (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BlakeRoundCached.native.genericQueries.get ⟨25, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.BlakeRoundCached.native.genericQueries ⟨25, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field25_0.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨150, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field25_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part3.generic_value25_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field25_1.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨151, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field25_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part3.generic_value25_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field25_2.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨152, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field25_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part3.generic_value25_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field25_3.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨153, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field25_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part3.generic_value25_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field25_4.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨154, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field25_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part3.generic_value25_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field25_5.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨155, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field25_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part3.generic_value25_5 physical data arithmetic).trans transported5
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BlakeRoundCached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BlakeRoundCached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Blake2Round" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.genericExpressions25, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BlakeRoundCached.native.model.Contains Airbender.Compiler.TableNative.BlakeRoundCached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part3.genericExpression25_0.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part3.genericExpression25_1.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part3.genericExpression25_2.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part3.genericExpression25_3.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part3.genericExpression25_4.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part3.genericExpression25_5.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5]
  exact valid

theorem generic_lookup26
    (sourceValue : Fin 763 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BlakeRoundCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BlakeRoundCached.native.assigned (Airbender.Compiler.HelperValidityNative.BlakeRoundCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BlakeRoundCached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.genericExpressions26).Contains (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BlakeRoundCached.native.genericQueries.get ⟨26, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.BlakeRoundCached.native.genericQueries ⟨26, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field26_0.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨156, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field26_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part3.generic_value26_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field26_1.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨157, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field26_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part3.generic_value26_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field26_2.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨158, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field26_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part3.generic_value26_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field26_3.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨159, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field26_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part3.generic_value26_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field26_4.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨160, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field26_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part3.generic_value26_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field26_5.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨161, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field26_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part3.generic_value26_5 physical data arithmetic).trans transported5
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BlakeRoundCached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BlakeRoundCached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Blake2Round" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.genericExpressions26, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BlakeRoundCached.native.model.Contains Airbender.Compiler.TableNative.BlakeRoundCached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part3.genericExpression26_0.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part3.genericExpression26_1.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part3.genericExpression26_2.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part3.genericExpression26_3.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part3.genericExpression26_4.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part3.genericExpression26_5.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5]
  exact valid

theorem generic_lookup27
    (sourceValue : Fin 763 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BlakeRoundCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BlakeRoundCached.native.assigned (Airbender.Compiler.HelperValidityNative.BlakeRoundCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BlakeRoundCached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.genericExpressions27).Contains (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BlakeRoundCached.native.genericQueries.get ⟨27, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.BlakeRoundCached.native.genericQueries ⟨27, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field27_0.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨162, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field27_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part3.generic_value27_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field27_1.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨163, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field27_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part3.generic_value27_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field27_2.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨164, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field27_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part3.generic_value27_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field27_3.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨165, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field27_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part3.generic_value27_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field27_4.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨166, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field27_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part3.generic_value27_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field27_5.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨167, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field27_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part3.generic_value27_5 physical data arithmetic).trans transported5
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BlakeRoundCached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BlakeRoundCached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Blake2Round" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.genericExpressions27, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BlakeRoundCached.native.model.Contains Airbender.Compiler.TableNative.BlakeRoundCached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part3.genericExpression27_0.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part3.genericExpression27_1.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part3.genericExpression27_2.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part3.genericExpression27_3.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part3.genericExpression27_4.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part3.genericExpression27_5.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5]
  exact valid

theorem generic_lookup28
    (sourceValue : Fin 763 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BlakeRoundCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BlakeRoundCached.native.assigned (Airbender.Compiler.HelperValidityNative.BlakeRoundCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BlakeRoundCached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.genericExpressions28).Contains (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BlakeRoundCached.native.genericQueries.get ⟨28, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.BlakeRoundCached.native.genericQueries ⟨28, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field28_0.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨168, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field28_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part3.generic_value28_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field28_1.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨169, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field28_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part3.generic_value28_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field28_2.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨170, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field28_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part3.generic_value28_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field28_3.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨171, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field28_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part3.generic_value28_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field28_4.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨172, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field28_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part3.generic_value28_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field28_5.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨173, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field28_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part3.generic_value28_5 physical data arithmetic).trans transported5
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BlakeRoundCached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BlakeRoundCached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Blake2Round" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.genericExpressions28, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BlakeRoundCached.native.model.Contains Airbender.Compiler.TableNative.BlakeRoundCached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part3.genericExpression28_0.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part3.genericExpression28_1.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part3.genericExpression28_2.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part3.genericExpression28_3.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part3.genericExpression28_4.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part3.genericExpression28_5.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5]
  exact valid

theorem generic_lookup29
    (sourceValue : Fin 763 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BlakeRoundCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BlakeRoundCached.native.assigned (Airbender.Compiler.HelperValidityNative.BlakeRoundCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BlakeRoundCached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.genericExpressions29).Contains (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BlakeRoundCached.native.genericQueries.get ⟨29, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.BlakeRoundCached.native.genericQueries ⟨29, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field29_0.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨174, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field29_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part3.generic_value29_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field29_1.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨175, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field29_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part3.generic_value29_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field29_2.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨176, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field29_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part3.generic_value29_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field29_3.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨177, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field29_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part3.generic_value29_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field29_4.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨178, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field29_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part3.generic_value29_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field29_5.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨179, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field29_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part3.generic_value29_5 physical data arithmetic).trans transported5
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BlakeRoundCached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BlakeRoundCached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Blake2Round" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.genericExpressions29, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BlakeRoundCached.native.model.Contains Airbender.Compiler.TableNative.BlakeRoundCached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part3.genericExpression29_0.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part3.genericExpression29_1.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part3.genericExpression29_2.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part3.genericExpression29_3.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part3.genericExpression29_4.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part3.genericExpression29_5.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5]
  exact valid

theorem generic_lookup30
    (sourceValue : Fin 763 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BlakeRoundCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BlakeRoundCached.native.assigned (Airbender.Compiler.HelperValidityNative.BlakeRoundCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BlakeRoundCached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.genericExpressions30).Contains (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BlakeRoundCached.native.genericQueries.get ⟨30, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.BlakeRoundCached.native.genericQueries ⟨30, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field30_0.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨180, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field30_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part3.generic_value30_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field30_1.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨181, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field30_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part3.generic_value30_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field30_2.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨182, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field30_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part3.generic_value30_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field30_3.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨183, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field30_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part3.generic_value30_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field30_4.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨184, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field30_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part3.generic_value30_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field30_5.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨185, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field30_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part3.generic_value30_5 physical data arithmetic).trans transported5
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BlakeRoundCached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BlakeRoundCached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Blake2Round" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.genericExpressions30, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BlakeRoundCached.native.model.Contains Airbender.Compiler.TableNative.BlakeRoundCached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part3.genericExpression30_0.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part3.genericExpression30_1.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part3.genericExpression30_2.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part3.genericExpression30_3.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part3.genericExpression30_4.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part3.genericExpression30_5.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5]
  exact valid

theorem generic_lookup31
    (sourceValue : Fin 763 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BlakeRoundCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BlakeRoundCached.native.assigned (Airbender.Compiler.HelperValidityNative.BlakeRoundCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BlakeRoundCached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.genericExpressions31).Contains (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BlakeRoundCached.native.genericQueries.get ⟨31, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.BlakeRoundCached.native.genericQueries ⟨31, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field31_0.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨186, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field31_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part3.generic_value31_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field31_1.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨187, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field31_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part3.generic_value31_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field31_2.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨188, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field31_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part3.generic_value31_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field31_3.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨189, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field31_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part3.generic_value31_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field31_4.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨190, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field31_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part3.generic_value31_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field31_5.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨191, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field31_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part3.generic_value31_5 physical data arithmetic).trans transported5
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BlakeRoundCached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BlakeRoundCached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Blake2Round" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.genericExpressions31, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BlakeRoundCached.native.model.Contains Airbender.Compiler.TableNative.BlakeRoundCached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part3.genericExpression31_0.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part3.genericExpression31_1.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part3.genericExpression31_2.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part3.genericExpression31_3.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part3.genericExpression31_4.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part3.genericExpression31_5.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5]
  exact valid


end Airbender.Compiler.CleanClosedNative.BlakeRoundCached
