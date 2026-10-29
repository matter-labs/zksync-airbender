import Airbender.Proofs.GKRProtocol.CleanClosedParts.BigintUncached.Shared

namespace Airbender.Compiler.CleanClosedNative.BigintUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

theorem generic_lookup32
    (sourceValue : Fin 276 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BigintUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BigintUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BigintUncached.native.assigned (Airbender.Compiler.HelperValidityNative.BigintUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BigintUncached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.genericExpressions32).Contains (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BigintUncached.native.genericQueries.get ⟨32, by decide⟩
  have member := authored.1 query (List.get_mem Airbender.Compiler.LookupSourceNative.BigintUncached.native.genericQueries ⟨32, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BigintUncached.native.field32_0.source ∈ Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields ⟨96, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintUncached.native.field32_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.generic_value32_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BigintUncached.native.field32_1.source ∈ Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields ⟨97, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintUncached.native.field32_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.generic_value32_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BigintUncached.native.field32_2.source ∈ Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields ⟨98, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintUncached.native.field32_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.generic_value32_2 physical data arithmetic).trans transported2
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BigintUncached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BigintUncached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Bigint" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.genericExpressions32, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BigintUncached.native.model.Contains Airbender.Compiler.TableNative.BigintUncached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.genericExpression32_0.eval (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.genericExpression32_1.eval (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.genericExpression32_2.eval (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data)]
  rw [same0, same1, same2]
  exact valid

theorem generic_lookup33
    (sourceValue : Fin 276 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BigintUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BigintUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BigintUncached.native.assigned (Airbender.Compiler.HelperValidityNative.BigintUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BigintUncached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.genericExpressions33).Contains (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BigintUncached.native.genericQueries.get ⟨33, by decide⟩
  have member := authored.1 query (List.get_mem Airbender.Compiler.LookupSourceNative.BigintUncached.native.genericQueries ⟨33, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BigintUncached.native.field33_0.source ∈ Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields ⟨99, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintUncached.native.field33_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.generic_value33_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BigintUncached.native.field33_1.source ∈ Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields ⟨100, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintUncached.native.field33_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.generic_value33_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BigintUncached.native.field33_2.source ∈ Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields ⟨101, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintUncached.native.field33_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.generic_value33_2 physical data arithmetic).trans transported2
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BigintUncached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BigintUncached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Bigint" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.genericExpressions33, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BigintUncached.native.model.Contains Airbender.Compiler.TableNative.BigintUncached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.genericExpression33_0.eval (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.genericExpression33_1.eval (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.genericExpression33_2.eval (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data)]
  rw [same0, same1, same2]
  exact valid

theorem generic_lookup34
    (sourceValue : Fin 276 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BigintUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BigintUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BigintUncached.native.assigned (Airbender.Compiler.HelperValidityNative.BigintUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BigintUncached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.genericExpressions34).Contains (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BigintUncached.native.genericQueries.get ⟨34, by decide⟩
  have member := authored.1 query (List.get_mem Airbender.Compiler.LookupSourceNative.BigintUncached.native.genericQueries ⟨34, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BigintUncached.native.field34_0.source ∈ Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields ⟨102, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintUncached.native.field34_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.generic_value34_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BigintUncached.native.field34_1.source ∈ Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields ⟨103, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintUncached.native.field34_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.generic_value34_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BigintUncached.native.field34_2.source ∈ Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields ⟨104, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintUncached.native.field34_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.generic_value34_2 physical data arithmetic).trans transported2
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BigintUncached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BigintUncached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Bigint" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.genericExpressions34, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BigintUncached.native.model.Contains Airbender.Compiler.TableNative.BigintUncached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.genericExpression34_0.eval (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.genericExpression34_1.eval (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.genericExpression34_2.eval (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data)]
  rw [same0, same1, same2]
  exact valid

theorem generic_lookup35
    (sourceValue : Fin 276 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BigintUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BigintUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BigintUncached.native.assigned (Airbender.Compiler.HelperValidityNative.BigintUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BigintUncached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.genericExpressions35).Contains (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BigintUncached.native.genericQueries.get ⟨35, by decide⟩
  have member := authored.1 query (List.get_mem Airbender.Compiler.LookupSourceNative.BigintUncached.native.genericQueries ⟨35, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BigintUncached.native.field35_0.source ∈ Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields ⟨105, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintUncached.native.field35_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.generic_value35_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BigintUncached.native.field35_1.source ∈ Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields ⟨106, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintUncached.native.field35_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.generic_value35_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BigintUncached.native.field35_2.source ∈ Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields ⟨107, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintUncached.native.field35_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.generic_value35_2 physical data arithmetic).trans transported2
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BigintUncached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BigintUncached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Bigint" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.genericExpressions35, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BigintUncached.native.model.Contains Airbender.Compiler.TableNative.BigintUncached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.genericExpression35_0.eval (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.genericExpression35_1.eval (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.genericExpression35_2.eval (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data)]
  rw [same0, same1, same2]
  exact valid

theorem generic_lookup36
    (sourceValue : Fin 276 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BigintUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BigintUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BigintUncached.native.assigned (Airbender.Compiler.HelperValidityNative.BigintUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BigintUncached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.genericExpressions36).Contains (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BigintUncached.native.genericQueries.get ⟨36, by decide⟩
  have member := authored.1 query (List.get_mem Airbender.Compiler.LookupSourceNative.BigintUncached.native.genericQueries ⟨36, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BigintUncached.native.field36_0.source ∈ Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields ⟨108, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintUncached.native.field36_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.generic_value36_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BigintUncached.native.field36_1.source ∈ Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields ⟨109, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintUncached.native.field36_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.generic_value36_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BigintUncached.native.field36_2.source ∈ Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields ⟨110, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintUncached.native.field36_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.generic_value36_2 physical data arithmetic).trans transported2
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BigintUncached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BigintUncached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Bigint" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.genericExpressions36, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BigintUncached.native.model.Contains Airbender.Compiler.TableNative.BigintUncached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.genericExpression36_0.eval (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.genericExpression36_1.eval (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.genericExpression36_2.eval (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data)]
  rw [same0, same1, same2]
  exact valid

theorem generic_lookup37
    (sourceValue : Fin 276 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BigintUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BigintUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BigintUncached.native.assigned (Airbender.Compiler.HelperValidityNative.BigintUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BigintUncached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.genericExpressions37).Contains (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BigintUncached.native.genericQueries.get ⟨37, by decide⟩
  have member := authored.1 query (List.get_mem Airbender.Compiler.LookupSourceNative.BigintUncached.native.genericQueries ⟨37, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BigintUncached.native.field37_0.source ∈ Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields ⟨111, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintUncached.native.field37_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.generic_value37_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BigintUncached.native.field37_1.source ∈ Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields ⟨112, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintUncached.native.field37_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.generic_value37_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BigintUncached.native.field37_2.source ∈ Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields ⟨113, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintUncached.native.field37_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.generic_value37_2 physical data arithmetic).trans transported2
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BigintUncached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BigintUncached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Bigint" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.genericExpressions37, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BigintUncached.native.model.Contains Airbender.Compiler.TableNative.BigintUncached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.genericExpression37_0.eval (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.genericExpression37_1.eval (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.genericExpression37_2.eval (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data)]
  rw [same0, same1, same2]
  exact valid

theorem generic_lookup38
    (sourceValue : Fin 276 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BigintUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BigintUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BigintUncached.native.assigned (Airbender.Compiler.HelperValidityNative.BigintUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BigintUncached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.genericExpressions38).Contains (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BigintUncached.native.genericQueries.get ⟨38, by decide⟩
  have member := authored.1 query (List.get_mem Airbender.Compiler.LookupSourceNative.BigintUncached.native.genericQueries ⟨38, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BigintUncached.native.field38_0.source ∈ Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields ⟨114, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintUncached.native.field38_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.generic_value38_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BigintUncached.native.field38_1.source ∈ Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields ⟨115, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintUncached.native.field38_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.generic_value38_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BigintUncached.native.field38_2.source ∈ Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields ⟨116, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintUncached.native.field38_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.generic_value38_2 physical data arithmetic).trans transported2
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BigintUncached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BigintUncached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Bigint" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.genericExpressions38, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BigintUncached.native.model.Contains Airbender.Compiler.TableNative.BigintUncached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.genericExpression38_0.eval (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.genericExpression38_1.eval (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.genericExpression38_2.eval (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data)]
  rw [same0, same1, same2]
  exact valid

theorem generic_lookup39
    (sourceValue : Fin 276 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BigintUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BigintUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BigintUncached.native.assigned (Airbender.Compiler.HelperValidityNative.BigintUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BigintUncached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.genericExpressions39).Contains (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BigintUncached.native.genericQueries.get ⟨39, by decide⟩
  have member := authored.1 query (List.get_mem Airbender.Compiler.LookupSourceNative.BigintUncached.native.genericQueries ⟨39, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BigintUncached.native.field39_0.source ∈ Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields ⟨117, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintUncached.native.field39_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.generic_value39_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BigintUncached.native.field39_1.source ∈ Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields ⟨118, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintUncached.native.field39_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.generic_value39_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BigintUncached.native.field39_2.source ∈ Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields ⟨119, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintUncached.native.field39_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.generic_value39_2 physical data arithmetic).trans transported2
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BigintUncached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BigintUncached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Bigint" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.genericExpressions39, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BigintUncached.native.model.Contains Airbender.Compiler.TableNative.BigintUncached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.genericExpression39_0.eval (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.genericExpression39_1.eval (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.genericExpression39_2.eval (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data)]
  rw [same0, same1, same2]
  exact valid


end Airbender.Compiler.CleanClosedNative.BigintUncached
