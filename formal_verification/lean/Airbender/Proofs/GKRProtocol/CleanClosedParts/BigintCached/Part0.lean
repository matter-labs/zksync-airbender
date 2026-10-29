import Airbender.Proofs.GKRProtocol.CleanClosedParts.BigintCached.Shared

namespace Airbender.Compiler.CleanClosedNative.BigintCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

theorem generic_lookup0
    (sourceValue : Fin 276 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BigintCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BigintCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BigintCached.native.assigned (Airbender.Compiler.HelperValidityNative.BigintCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BigintCached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.genericExpressions0).Contains (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BigintCached.native.genericQueries.get ⟨0, by decide⟩
  have member := authored.1 query (List.get_mem Airbender.Compiler.LookupSourceNative.BigintCached.native.genericQueries ⟨0, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BigintCached.native.field0_0.source ∈ Airbender.Compiler.QueryFrameNative.BigintCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintCached.native.fields ⟨0, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BigintCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintCached.native.field0_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part0.generic_value0_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BigintCached.native.field0_1.source ∈ Airbender.Compiler.QueryFrameNative.BigintCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintCached.native.fields ⟨1, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BigintCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintCached.native.field0_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part0.generic_value0_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BigintCached.native.field0_2.source ∈ Airbender.Compiler.QueryFrameNative.BigintCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintCached.native.fields ⟨2, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BigintCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintCached.native.field0_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part0.generic_value0_2 physical data arithmetic).trans transported2
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BigintCached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BigintCached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Bigint" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.genericExpressions0, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BigintCached.native.model.Contains Airbender.Compiler.TableNative.BigintCached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part0.genericExpression0_0.eval (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part0.genericExpression0_1.eval (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part0.genericExpression0_2.eval (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data)]
  rw [same0, same1, same2]
  exact valid

theorem generic_lookup1
    (sourceValue : Fin 276 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BigintCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BigintCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BigintCached.native.assigned (Airbender.Compiler.HelperValidityNative.BigintCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BigintCached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.genericExpressions1).Contains (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BigintCached.native.genericQueries.get ⟨1, by decide⟩
  have member := authored.1 query (List.get_mem Airbender.Compiler.LookupSourceNative.BigintCached.native.genericQueries ⟨1, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BigintCached.native.field1_0.source ∈ Airbender.Compiler.QueryFrameNative.BigintCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintCached.native.fields ⟨3, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BigintCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintCached.native.field1_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part0.generic_value1_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BigintCached.native.field1_1.source ∈ Airbender.Compiler.QueryFrameNative.BigintCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintCached.native.fields ⟨4, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BigintCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintCached.native.field1_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part0.generic_value1_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BigintCached.native.field1_2.source ∈ Airbender.Compiler.QueryFrameNative.BigintCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintCached.native.fields ⟨5, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BigintCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintCached.native.field1_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part0.generic_value1_2 physical data arithmetic).trans transported2
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BigintCached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BigintCached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Bigint" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.genericExpressions1, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BigintCached.native.model.Contains Airbender.Compiler.TableNative.BigintCached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part0.genericExpression1_0.eval (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part0.genericExpression1_1.eval (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part0.genericExpression1_2.eval (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data)]
  rw [same0, same1, same2]
  exact valid

theorem generic_lookup2
    (sourceValue : Fin 276 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BigintCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BigintCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BigintCached.native.assigned (Airbender.Compiler.HelperValidityNative.BigintCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BigintCached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.genericExpressions2).Contains (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BigintCached.native.genericQueries.get ⟨2, by decide⟩
  have member := authored.1 query (List.get_mem Airbender.Compiler.LookupSourceNative.BigintCached.native.genericQueries ⟨2, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BigintCached.native.field2_0.source ∈ Airbender.Compiler.QueryFrameNative.BigintCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintCached.native.fields ⟨6, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BigintCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintCached.native.field2_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part0.generic_value2_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BigintCached.native.field2_1.source ∈ Airbender.Compiler.QueryFrameNative.BigintCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintCached.native.fields ⟨7, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BigintCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintCached.native.field2_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part0.generic_value2_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BigintCached.native.field2_2.source ∈ Airbender.Compiler.QueryFrameNative.BigintCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintCached.native.fields ⟨8, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BigintCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintCached.native.field2_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part0.generic_value2_2 physical data arithmetic).trans transported2
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BigintCached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BigintCached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Bigint" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.genericExpressions2, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BigintCached.native.model.Contains Airbender.Compiler.TableNative.BigintCached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part0.genericExpression2_0.eval (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part0.genericExpression2_1.eval (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part0.genericExpression2_2.eval (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data)]
  rw [same0, same1, same2]
  exact valid

theorem generic_lookup3
    (sourceValue : Fin 276 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BigintCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BigintCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BigintCached.native.assigned (Airbender.Compiler.HelperValidityNative.BigintCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BigintCached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.genericExpressions3).Contains (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BigintCached.native.genericQueries.get ⟨3, by decide⟩
  have member := authored.1 query (List.get_mem Airbender.Compiler.LookupSourceNative.BigintCached.native.genericQueries ⟨3, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BigintCached.native.field3_0.source ∈ Airbender.Compiler.QueryFrameNative.BigintCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintCached.native.fields ⟨9, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BigintCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintCached.native.field3_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part0.generic_value3_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BigintCached.native.field3_1.source ∈ Airbender.Compiler.QueryFrameNative.BigintCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintCached.native.fields ⟨10, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BigintCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintCached.native.field3_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part0.generic_value3_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BigintCached.native.field3_2.source ∈ Airbender.Compiler.QueryFrameNative.BigintCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintCached.native.fields ⟨11, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BigintCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintCached.native.field3_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part0.generic_value3_2 physical data arithmetic).trans transported2
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BigintCached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BigintCached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Bigint" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.genericExpressions3, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BigintCached.native.model.Contains Airbender.Compiler.TableNative.BigintCached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part0.genericExpression3_0.eval (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part0.genericExpression3_1.eval (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part0.genericExpression3_2.eval (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data)]
  rw [same0, same1, same2]
  exact valid

theorem generic_lookup4
    (sourceValue : Fin 276 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BigintCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BigintCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BigintCached.native.assigned (Airbender.Compiler.HelperValidityNative.BigintCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BigintCached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.genericExpressions4).Contains (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BigintCached.native.genericQueries.get ⟨4, by decide⟩
  have member := authored.1 query (List.get_mem Airbender.Compiler.LookupSourceNative.BigintCached.native.genericQueries ⟨4, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BigintCached.native.field4_0.source ∈ Airbender.Compiler.QueryFrameNative.BigintCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintCached.native.fields ⟨12, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BigintCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintCached.native.field4_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part0.generic_value4_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BigintCached.native.field4_1.source ∈ Airbender.Compiler.QueryFrameNative.BigintCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintCached.native.fields ⟨13, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BigintCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintCached.native.field4_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part0.generic_value4_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BigintCached.native.field4_2.source ∈ Airbender.Compiler.QueryFrameNative.BigintCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintCached.native.fields ⟨14, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BigintCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintCached.native.field4_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part0.generic_value4_2 physical data arithmetic).trans transported2
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BigintCached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BigintCached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Bigint" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.genericExpressions4, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BigintCached.native.model.Contains Airbender.Compiler.TableNative.BigintCached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part0.genericExpression4_0.eval (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part0.genericExpression4_1.eval (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part0.genericExpression4_2.eval (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data)]
  rw [same0, same1, same2]
  exact valid

theorem generic_lookup5
    (sourceValue : Fin 276 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BigintCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BigintCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BigintCached.native.assigned (Airbender.Compiler.HelperValidityNative.BigintCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BigintCached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.genericExpressions5).Contains (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BigintCached.native.genericQueries.get ⟨5, by decide⟩
  have member := authored.1 query (List.get_mem Airbender.Compiler.LookupSourceNative.BigintCached.native.genericQueries ⟨5, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BigintCached.native.field5_0.source ∈ Airbender.Compiler.QueryFrameNative.BigintCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintCached.native.fields ⟨15, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BigintCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintCached.native.field5_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part0.generic_value5_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BigintCached.native.field5_1.source ∈ Airbender.Compiler.QueryFrameNative.BigintCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintCached.native.fields ⟨16, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BigintCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintCached.native.field5_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part0.generic_value5_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BigintCached.native.field5_2.source ∈ Airbender.Compiler.QueryFrameNative.BigintCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintCached.native.fields ⟨17, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BigintCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintCached.native.field5_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part0.generic_value5_2 physical data arithmetic).trans transported2
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BigintCached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BigintCached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Bigint" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.genericExpressions5, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BigintCached.native.model.Contains Airbender.Compiler.TableNative.BigintCached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part0.genericExpression5_0.eval (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part0.genericExpression5_1.eval (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part0.genericExpression5_2.eval (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data)]
  rw [same0, same1, same2]
  exact valid

theorem generic_lookup6
    (sourceValue : Fin 276 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BigintCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BigintCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BigintCached.native.assigned (Airbender.Compiler.HelperValidityNative.BigintCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BigintCached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.genericExpressions6).Contains (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BigintCached.native.genericQueries.get ⟨6, by decide⟩
  have member := authored.1 query (List.get_mem Airbender.Compiler.LookupSourceNative.BigintCached.native.genericQueries ⟨6, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BigintCached.native.field6_0.source ∈ Airbender.Compiler.QueryFrameNative.BigintCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintCached.native.fields ⟨18, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BigintCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintCached.native.field6_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part0.generic_value6_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BigintCached.native.field6_1.source ∈ Airbender.Compiler.QueryFrameNative.BigintCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintCached.native.fields ⟨19, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BigintCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintCached.native.field6_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part0.generic_value6_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BigintCached.native.field6_2.source ∈ Airbender.Compiler.QueryFrameNative.BigintCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintCached.native.fields ⟨20, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BigintCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintCached.native.field6_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part0.generic_value6_2 physical data arithmetic).trans transported2
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BigintCached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BigintCached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Bigint" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.genericExpressions6, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BigintCached.native.model.Contains Airbender.Compiler.TableNative.BigintCached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part0.genericExpression6_0.eval (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part0.genericExpression6_1.eval (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part0.genericExpression6_2.eval (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data)]
  rw [same0, same1, same2]
  exact valid

theorem generic_lookup7
    (sourceValue : Fin 276 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BigintCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BigintCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BigintCached.native.assigned (Airbender.Compiler.HelperValidityNative.BigintCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BigintCached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.genericExpressions7).Contains (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BigintCached.native.genericQueries.get ⟨7, by decide⟩
  have member := authored.1 query (List.get_mem Airbender.Compiler.LookupSourceNative.BigintCached.native.genericQueries ⟨7, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BigintCached.native.field7_0.source ∈ Airbender.Compiler.QueryFrameNative.BigintCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintCached.native.fields ⟨21, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BigintCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintCached.native.field7_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part0.generic_value7_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BigintCached.native.field7_1.source ∈ Airbender.Compiler.QueryFrameNative.BigintCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintCached.native.fields ⟨22, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BigintCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintCached.native.field7_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part0.generic_value7_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BigintCached.native.field7_2.source ∈ Airbender.Compiler.QueryFrameNative.BigintCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintCached.native.fields ⟨23, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BigintCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintCached.native.field7_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part0.generic_value7_2 physical data arithmetic).trans transported2
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BigintCached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BigintCached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Bigint" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.genericExpressions7, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BigintCached.native.model.Contains Airbender.Compiler.TableNative.BigintCached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part0.genericExpression7_0.eval (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part0.genericExpression7_1.eval (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part0.genericExpression7_2.eval (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data)]
  rw [same0, same1, same2]
  exact valid


end Airbender.Compiler.CleanClosedNative.BigintCached
