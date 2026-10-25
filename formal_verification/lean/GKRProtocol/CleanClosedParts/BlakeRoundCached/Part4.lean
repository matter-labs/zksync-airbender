import GKRProtocol.CleanClosedParts.BlakeRoundCached.Shared

namespace Airbender.Compiler.CleanClosedNative.BlakeRoundCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

theorem generic_lookup32
    (sourceValue : Fin 763 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BlakeRoundCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BlakeRoundCached.native.assigned (Airbender.Compiler.HelperValidityNative.BlakeRoundCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BlakeRoundCached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.genericExpressions32).Contains (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BlakeRoundCached.native.genericQueries.get ⟨32, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.BlakeRoundCached.native.genericQueries ⟨32, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field32_0.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨192, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field32_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part4.generic_value32_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field32_1.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨193, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field32_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part4.generic_value32_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field32_2.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨194, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field32_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part4.generic_value32_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field32_3.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨195, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field32_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part4.generic_value32_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field32_4.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨196, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field32_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part4.generic_value32_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field32_5.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨197, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field32_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part4.generic_value32_5 physical data arithmetic).trans transported5
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BlakeRoundCached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BlakeRoundCached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Blake2Round" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.genericExpressions32, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BlakeRoundCached.native.model.Contains Airbender.Compiler.TableNative.BlakeRoundCached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part4.genericExpression32_0.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part4.genericExpression32_1.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part4.genericExpression32_2.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part4.genericExpression32_3.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part4.genericExpression32_4.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part4.genericExpression32_5.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5]
  exact valid

theorem generic_lookup33
    (sourceValue : Fin 763 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BlakeRoundCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BlakeRoundCached.native.assigned (Airbender.Compiler.HelperValidityNative.BlakeRoundCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BlakeRoundCached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.genericExpressions33).Contains (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BlakeRoundCached.native.genericQueries.get ⟨33, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.BlakeRoundCached.native.genericQueries ⟨33, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field33_0.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨198, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field33_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part4.generic_value33_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field33_1.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨199, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field33_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part4.generic_value33_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field33_2.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨200, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field33_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part4.generic_value33_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field33_3.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨201, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field33_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part4.generic_value33_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field33_4.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨202, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field33_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part4.generic_value33_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field33_5.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨203, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field33_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part4.generic_value33_5 physical data arithmetic).trans transported5
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BlakeRoundCached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BlakeRoundCached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Blake2Round" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.genericExpressions33, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BlakeRoundCached.native.model.Contains Airbender.Compiler.TableNative.BlakeRoundCached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part4.genericExpression33_0.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part4.genericExpression33_1.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part4.genericExpression33_2.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part4.genericExpression33_3.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part4.genericExpression33_4.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part4.genericExpression33_5.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5]
  exact valid

theorem generic_lookup34
    (sourceValue : Fin 763 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BlakeRoundCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BlakeRoundCached.native.assigned (Airbender.Compiler.HelperValidityNative.BlakeRoundCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BlakeRoundCached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.genericExpressions34).Contains (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BlakeRoundCached.native.genericQueries.get ⟨34, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.BlakeRoundCached.native.genericQueries ⟨34, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field34_0.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨204, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field34_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part4.generic_value34_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field34_1.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨205, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field34_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part4.generic_value34_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field34_2.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨206, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field34_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part4.generic_value34_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field34_3.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨207, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field34_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part4.generic_value34_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field34_4.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨208, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field34_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part4.generic_value34_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field34_5.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨209, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field34_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part4.generic_value34_5 physical data arithmetic).trans transported5
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BlakeRoundCached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BlakeRoundCached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Blake2Round" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.genericExpressions34, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BlakeRoundCached.native.model.Contains Airbender.Compiler.TableNative.BlakeRoundCached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part4.genericExpression34_0.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part4.genericExpression34_1.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part4.genericExpression34_2.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part4.genericExpression34_3.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part4.genericExpression34_4.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part4.genericExpression34_5.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5]
  exact valid

theorem generic_lookup35
    (sourceValue : Fin 763 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BlakeRoundCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BlakeRoundCached.native.assigned (Airbender.Compiler.HelperValidityNative.BlakeRoundCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BlakeRoundCached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.genericExpressions35).Contains (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BlakeRoundCached.native.genericQueries.get ⟨35, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.BlakeRoundCached.native.genericQueries ⟨35, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field35_0.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨210, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field35_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part4.generic_value35_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field35_1.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨211, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field35_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part4.generic_value35_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field35_2.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨212, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field35_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part4.generic_value35_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field35_3.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨213, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field35_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part4.generic_value35_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field35_4.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨214, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field35_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part4.generic_value35_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field35_5.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨215, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field35_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part4.generic_value35_5 physical data arithmetic).trans transported5
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BlakeRoundCached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BlakeRoundCached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Blake2Round" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.genericExpressions35, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BlakeRoundCached.native.model.Contains Airbender.Compiler.TableNative.BlakeRoundCached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part4.genericExpression35_0.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part4.genericExpression35_1.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part4.genericExpression35_2.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part4.genericExpression35_3.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part4.genericExpression35_4.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part4.genericExpression35_5.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5]
  exact valid

theorem generic_lookup36
    (sourceValue : Fin 763 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BlakeRoundCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BlakeRoundCached.native.assigned (Airbender.Compiler.HelperValidityNative.BlakeRoundCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BlakeRoundCached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.genericExpressions36).Contains (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BlakeRoundCached.native.genericQueries.get ⟨36, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.BlakeRoundCached.native.genericQueries ⟨36, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field36_0.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨216, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field36_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part4.generic_value36_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field36_1.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨217, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field36_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part4.generic_value36_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field36_2.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨218, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field36_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part4.generic_value36_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field36_3.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨219, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field36_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part4.generic_value36_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field36_4.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨220, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field36_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part4.generic_value36_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field36_5.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨221, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field36_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part4.generic_value36_5 physical data arithmetic).trans transported5
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BlakeRoundCached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BlakeRoundCached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Blake2Round" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.genericExpressions36, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BlakeRoundCached.native.model.Contains Airbender.Compiler.TableNative.BlakeRoundCached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part4.genericExpression36_0.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part4.genericExpression36_1.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part4.genericExpression36_2.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part4.genericExpression36_3.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part4.genericExpression36_4.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part4.genericExpression36_5.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5]
  exact valid

theorem generic_lookup37
    (sourceValue : Fin 763 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BlakeRoundCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BlakeRoundCached.native.assigned (Airbender.Compiler.HelperValidityNative.BlakeRoundCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BlakeRoundCached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.genericExpressions37).Contains (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BlakeRoundCached.native.genericQueries.get ⟨37, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.BlakeRoundCached.native.genericQueries ⟨37, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field37_0.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨222, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field37_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part4.generic_value37_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field37_1.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨223, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field37_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part4.generic_value37_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field37_2.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨224, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field37_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part4.generic_value37_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field37_3.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨225, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field37_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part4.generic_value37_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field37_4.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨226, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field37_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part4.generic_value37_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field37_5.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨227, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field37_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part4.generic_value37_5 physical data arithmetic).trans transported5
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BlakeRoundCached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BlakeRoundCached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Blake2Round" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.genericExpressions37, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BlakeRoundCached.native.model.Contains Airbender.Compiler.TableNative.BlakeRoundCached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part4.genericExpression37_0.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part4.genericExpression37_1.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part4.genericExpression37_2.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part4.genericExpression37_3.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part4.genericExpression37_4.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part4.genericExpression37_5.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5]
  exact valid

theorem generic_lookup38
    (sourceValue : Fin 763 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BlakeRoundCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BlakeRoundCached.native.assigned (Airbender.Compiler.HelperValidityNative.BlakeRoundCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BlakeRoundCached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.genericExpressions38).Contains (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BlakeRoundCached.native.genericQueries.get ⟨38, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.BlakeRoundCached.native.genericQueries ⟨38, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field38_0.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨228, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field38_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part4.generic_value38_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field38_1.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨229, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field38_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part4.generic_value38_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field38_2.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨230, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field38_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part4.generic_value38_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field38_3.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨231, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field38_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part4.generic_value38_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field38_4.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨232, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field38_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part4.generic_value38_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field38_5.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨233, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field38_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part4.generic_value38_5 physical data arithmetic).trans transported5
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BlakeRoundCached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BlakeRoundCached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Blake2Round" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.genericExpressions38, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BlakeRoundCached.native.model.Contains Airbender.Compiler.TableNative.BlakeRoundCached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part4.genericExpression38_0.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part4.genericExpression38_1.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part4.genericExpression38_2.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part4.genericExpression38_3.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part4.genericExpression38_4.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part4.genericExpression38_5.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5]
  exact valid

theorem generic_lookup39
    (sourceValue : Fin 763 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BlakeRoundCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BlakeRoundCached.native.assigned (Airbender.Compiler.HelperValidityNative.BlakeRoundCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BlakeRoundCached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.genericExpressions39).Contains (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BlakeRoundCached.native.genericQueries.get ⟨39, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.BlakeRoundCached.native.genericQueries ⟨39, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field39_0.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨234, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field39_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part4.generic_value39_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field39_1.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨235, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field39_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part4.generic_value39_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field39_2.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨236, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field39_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part4.generic_value39_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field39_3.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨237, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field39_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part4.generic_value39_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field39_4.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨238, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field39_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part4.generic_value39_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field39_5.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨239, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field39_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part4.generic_value39_5 physical data arithmetic).trans transported5
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BlakeRoundCached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BlakeRoundCached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Blake2Round" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.genericExpressions39, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BlakeRoundCached.native.model.Contains Airbender.Compiler.TableNative.BlakeRoundCached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part4.genericExpression39_0.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part4.genericExpression39_1.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part4.genericExpression39_2.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part4.genericExpression39_3.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part4.genericExpression39_4.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part4.genericExpression39_5.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5]
  exact valid


end Airbender.Compiler.CleanClosedNative.BlakeRoundCached
