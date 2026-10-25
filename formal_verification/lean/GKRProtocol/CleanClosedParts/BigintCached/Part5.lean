import GKRProtocol.CleanClosedParts.BigintCached.Shared

namespace Airbender.Compiler.CleanClosedNative.BigintCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

theorem generic_lookup40
    (sourceValue : Fin 277 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BigintCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BigintCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BigintCached.native.assigned (Airbender.Compiler.HelperValidityNative.BigintCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BigintCached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.genericExpressions40).Contains (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BigintCached.native.genericQueries.get ⟨40, by decide⟩
  have member := authored.1 query (List.get_mem Airbender.Compiler.LookupSourceNative.BigintCached.native.genericQueries ⟨40, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BigintCached.native.field40_0.source ∈ Airbender.Compiler.QueryFrameNative.BigintCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintCached.native.fields ⟨120, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BigintCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintCached.native.field40_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part5.generic_value40_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BigintCached.native.field40_1.source ∈ Airbender.Compiler.QueryFrameNative.BigintCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintCached.native.fields ⟨121, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BigintCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintCached.native.field40_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part5.generic_value40_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BigintCached.native.field40_2.source ∈ Airbender.Compiler.QueryFrameNative.BigintCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintCached.native.fields ⟨122, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BigintCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintCached.native.field40_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part5.generic_value40_2 physical data arithmetic).trans transported2
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BigintCached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BigintCached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Bigint" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.genericExpressions40, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BigintCached.native.model.Contains Airbender.Compiler.TableNative.BigintCached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part5.genericExpression40_0.eval (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part5.genericExpression40_1.eval (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part5.genericExpression40_2.eval (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data)]
  rw [same0, same1, same2]
  exact valid

theorem generic_lookup41
    (sourceValue : Fin 277 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BigintCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BigintCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BigintCached.native.assigned (Airbender.Compiler.HelperValidityNative.BigintCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BigintCached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.genericExpressions41).Contains (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BigintCached.native.genericQueries.get ⟨41, by decide⟩
  have member := authored.1 query (List.get_mem Airbender.Compiler.LookupSourceNative.BigintCached.native.genericQueries ⟨41, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BigintCached.native.field41_0.source ∈ Airbender.Compiler.QueryFrameNative.BigintCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintCached.native.fields ⟨123, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BigintCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintCached.native.field41_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part5.generic_value41_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BigintCached.native.field41_1.source ∈ Airbender.Compiler.QueryFrameNative.BigintCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintCached.native.fields ⟨124, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BigintCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintCached.native.field41_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part5.generic_value41_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BigintCached.native.field41_2.source ∈ Airbender.Compiler.QueryFrameNative.BigintCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintCached.native.fields ⟨125, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BigintCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintCached.native.field41_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part5.generic_value41_2 physical data arithmetic).trans transported2
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BigintCached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BigintCached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Bigint" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.genericExpressions41, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BigintCached.native.model.Contains Airbender.Compiler.TableNative.BigintCached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part5.genericExpression41_0.eval (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part5.genericExpression41_1.eval (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part5.genericExpression41_2.eval (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data)]
  rw [same0, same1, same2]
  exact valid

theorem generic_lookup42
    (sourceValue : Fin 277 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BigintCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BigintCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BigintCached.native.assigned (Airbender.Compiler.HelperValidityNative.BigintCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BigintCached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.genericExpressions42).Contains (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BigintCached.native.genericQueries.get ⟨42, by decide⟩
  have member := authored.1 query (List.get_mem Airbender.Compiler.LookupSourceNative.BigintCached.native.genericQueries ⟨42, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BigintCached.native.field42_0.source ∈ Airbender.Compiler.QueryFrameNative.BigintCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintCached.native.fields ⟨126, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BigintCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintCached.native.field42_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part5.generic_value42_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BigintCached.native.field42_1.source ∈ Airbender.Compiler.QueryFrameNative.BigintCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintCached.native.fields ⟨127, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BigintCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintCached.native.field42_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part5.generic_value42_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BigintCached.native.field42_2.source ∈ Airbender.Compiler.QueryFrameNative.BigintCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintCached.native.fields ⟨128, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BigintCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintCached.native.field42_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part5.generic_value42_2 physical data arithmetic).trans transported2
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BigintCached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BigintCached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Bigint" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.genericExpressions42, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BigintCached.native.model.Contains Airbender.Compiler.TableNative.BigintCached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part5.genericExpression42_0.eval (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part5.genericExpression42_1.eval (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part5.genericExpression42_2.eval (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data)]
  rw [same0, same1, same2]
  exact valid

theorem generic_lookup43
    (sourceValue : Fin 277 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BigintCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BigintCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BigintCached.native.assigned (Airbender.Compiler.HelperValidityNative.BigintCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BigintCached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.genericExpressions43).Contains (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BigintCached.native.genericQueries.get ⟨43, by decide⟩
  have member := authored.1 query (List.get_mem Airbender.Compiler.LookupSourceNative.BigintCached.native.genericQueries ⟨43, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BigintCached.native.field43_0.source ∈ Airbender.Compiler.QueryFrameNative.BigintCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintCached.native.fields ⟨129, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BigintCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintCached.native.field43_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part5.generic_value43_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BigintCached.native.field43_1.source ∈ Airbender.Compiler.QueryFrameNative.BigintCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintCached.native.fields ⟨130, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BigintCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintCached.native.field43_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part5.generic_value43_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BigintCached.native.field43_2.source ∈ Airbender.Compiler.QueryFrameNative.BigintCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintCached.native.fields ⟨131, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BigintCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintCached.native.field43_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part5.generic_value43_2 physical data arithmetic).trans transported2
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BigintCached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BigintCached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Bigint" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.genericExpressions43, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BigintCached.native.model.Contains Airbender.Compiler.TableNative.BigintCached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part5.genericExpression43_0.eval (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part5.genericExpression43_1.eval (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part5.genericExpression43_2.eval (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data)]
  rw [same0, same1, same2]
  exact valid

theorem generic_lookup44
    (sourceValue : Fin 277 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BigintCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BigintCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BigintCached.native.assigned (Airbender.Compiler.HelperValidityNative.BigintCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BigintCached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.genericExpressions44).Contains (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BigintCached.native.genericQueries.get ⟨44, by decide⟩
  have member := authored.1 query (List.get_mem Airbender.Compiler.LookupSourceNative.BigintCached.native.genericQueries ⟨44, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BigintCached.native.field44_0.source ∈ Airbender.Compiler.QueryFrameNative.BigintCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintCached.native.fields ⟨132, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BigintCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintCached.native.field44_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part5.generic_value44_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BigintCached.native.field44_1.source ∈ Airbender.Compiler.QueryFrameNative.BigintCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintCached.native.fields ⟨133, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BigintCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintCached.native.field44_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part5.generic_value44_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BigintCached.native.field44_2.source ∈ Airbender.Compiler.QueryFrameNative.BigintCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintCached.native.fields ⟨134, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BigintCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintCached.native.field44_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part5.generic_value44_2 physical data arithmetic).trans transported2
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BigintCached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BigintCached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Bigint" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.genericExpressions44, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BigintCached.native.model.Contains Airbender.Compiler.TableNative.BigintCached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part5.genericExpression44_0.eval (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part5.genericExpression44_1.eval (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part5.genericExpression44_2.eval (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data)]
  rw [same0, same1, same2]
  exact valid

theorem generic_lookup45
    (sourceValue : Fin 277 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BigintCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BigintCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BigintCached.native.assigned (Airbender.Compiler.HelperValidityNative.BigintCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BigintCached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.genericExpressions45).Contains (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BigintCached.native.genericQueries.get ⟨45, by decide⟩
  have member := authored.1 query (List.get_mem Airbender.Compiler.LookupSourceNative.BigintCached.native.genericQueries ⟨45, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BigintCached.native.field45_0.source ∈ Airbender.Compiler.QueryFrameNative.BigintCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintCached.native.fields ⟨135, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BigintCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintCached.native.field45_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part5.generic_value45_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BigintCached.native.field45_1.source ∈ Airbender.Compiler.QueryFrameNative.BigintCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintCached.native.fields ⟨136, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BigintCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintCached.native.field45_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part5.generic_value45_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BigintCached.native.field45_2.source ∈ Airbender.Compiler.QueryFrameNative.BigintCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintCached.native.fields ⟨137, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BigintCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintCached.native.field45_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part5.generic_value45_2 physical data arithmetic).trans transported2
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BigintCached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BigintCached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Bigint" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.genericExpressions45, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BigintCached.native.model.Contains Airbender.Compiler.TableNative.BigintCached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part5.genericExpression45_0.eval (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part5.genericExpression45_1.eval (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part5.genericExpression45_2.eval (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data)]
  rw [same0, same1, same2]
  exact valid

theorem generic_lookup46
    (sourceValue : Fin 277 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BigintCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BigintCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BigintCached.native.assigned (Airbender.Compiler.HelperValidityNative.BigintCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BigintCached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.genericExpressions46).Contains (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BigintCached.native.genericQueries.get ⟨46, by decide⟩
  have member := authored.1 query (List.get_mem Airbender.Compiler.LookupSourceNative.BigintCached.native.genericQueries ⟨46, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BigintCached.native.field46_0.source ∈ Airbender.Compiler.QueryFrameNative.BigintCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintCached.native.fields ⟨138, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BigintCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintCached.native.field46_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part5.generic_value46_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BigintCached.native.field46_1.source ∈ Airbender.Compiler.QueryFrameNative.BigintCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintCached.native.fields ⟨139, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BigintCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintCached.native.field46_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part5.generic_value46_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BigintCached.native.field46_2.source ∈ Airbender.Compiler.QueryFrameNative.BigintCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintCached.native.fields ⟨140, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BigintCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintCached.native.field46_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part5.generic_value46_2 physical data arithmetic).trans transported2
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BigintCached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BigintCached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Bigint" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.genericExpressions46, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BigintCached.native.model.Contains Airbender.Compiler.TableNative.BigintCached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part5.genericExpression46_0.eval (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part5.genericExpression46_1.eval (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part5.genericExpression46_2.eval (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data)]
  rw [same0, same1, same2]
  exact valid

theorem generic_lookup47
    (sourceValue : Fin 277 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BigintCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BigintCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BigintCached.native.assigned (Airbender.Compiler.HelperValidityNative.BigintCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BigintCached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.genericExpressions47).Contains (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BigintCached.native.genericQueries.get ⟨47, by decide⟩
  have member := authored.1 query (List.get_mem Airbender.Compiler.LookupSourceNative.BigintCached.native.genericQueries ⟨47, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BigintCached.native.field47_0.source ∈ Airbender.Compiler.QueryFrameNative.BigintCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintCached.native.fields ⟨141, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BigintCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintCached.native.field47_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part5.generic_value47_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BigintCached.native.field47_1.source ∈ Airbender.Compiler.QueryFrameNative.BigintCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintCached.native.fields ⟨142, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BigintCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintCached.native.field47_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part5.generic_value47_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BigintCached.native.field47_2.source ∈ Airbender.Compiler.QueryFrameNative.BigintCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintCached.native.fields ⟨143, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BigintCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintCached.native.field47_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part5.generic_value47_2 physical data arithmetic).trans transported2
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BigintCached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BigintCached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Bigint" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.genericExpressions47, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BigintCached.native.model.Contains Airbender.Compiler.TableNative.BigintCached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part5.genericExpression47_0.eval (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part5.genericExpression47_1.eval (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part5.genericExpression47_2.eval (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data)]
  rw [same0, same1, same2]
  exact valid


end Airbender.Compiler.CleanClosedNative.BigintCached
