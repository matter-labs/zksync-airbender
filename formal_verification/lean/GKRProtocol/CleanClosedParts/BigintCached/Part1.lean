import GKRProtocol.CleanClosedParts.BigintCached.Shared

namespace Airbender.Compiler.CleanClosedNative.BigintCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

theorem generic_lookup8
    (sourceValue : Fin 277 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BigintCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BigintCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BigintCached.native.assigned (Airbender.Compiler.HelperValidityNative.BigintCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BigintCached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.genericExpressions8).Contains (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BigintCached.native.genericQueries.get ⟨8, by decide⟩
  have member := authored.1 query (List.get_mem Airbender.Compiler.LookupSourceNative.BigintCached.native.genericQueries ⟨8, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BigintCached.native.field8_0.source ∈ Airbender.Compiler.QueryFrameNative.BigintCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintCached.native.fields ⟨24, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BigintCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintCached.native.field8_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part1.generic_value8_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BigintCached.native.field8_1.source ∈ Airbender.Compiler.QueryFrameNative.BigintCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintCached.native.fields ⟨25, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BigintCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintCached.native.field8_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part1.generic_value8_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BigintCached.native.field8_2.source ∈ Airbender.Compiler.QueryFrameNative.BigintCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintCached.native.fields ⟨26, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BigintCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintCached.native.field8_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part1.generic_value8_2 physical data arithmetic).trans transported2
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BigintCached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BigintCached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Bigint" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.genericExpressions8, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BigintCached.native.model.Contains Airbender.Compiler.TableNative.BigintCached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part1.genericExpression8_0.eval (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part1.genericExpression8_1.eval (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part1.genericExpression8_2.eval (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data)]
  rw [same0, same1, same2]
  exact valid

theorem generic_lookup9
    (sourceValue : Fin 277 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BigintCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BigintCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BigintCached.native.assigned (Airbender.Compiler.HelperValidityNative.BigintCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BigintCached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.genericExpressions9).Contains (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BigintCached.native.genericQueries.get ⟨9, by decide⟩
  have member := authored.1 query (List.get_mem Airbender.Compiler.LookupSourceNative.BigintCached.native.genericQueries ⟨9, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BigintCached.native.field9_0.source ∈ Airbender.Compiler.QueryFrameNative.BigintCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintCached.native.fields ⟨27, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BigintCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintCached.native.field9_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part1.generic_value9_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BigintCached.native.field9_1.source ∈ Airbender.Compiler.QueryFrameNative.BigintCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintCached.native.fields ⟨28, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BigintCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintCached.native.field9_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part1.generic_value9_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BigintCached.native.field9_2.source ∈ Airbender.Compiler.QueryFrameNative.BigintCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintCached.native.fields ⟨29, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BigintCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintCached.native.field9_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part1.generic_value9_2 physical data arithmetic).trans transported2
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BigintCached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BigintCached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Bigint" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.genericExpressions9, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BigintCached.native.model.Contains Airbender.Compiler.TableNative.BigintCached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part1.genericExpression9_0.eval (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part1.genericExpression9_1.eval (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part1.genericExpression9_2.eval (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data)]
  rw [same0, same1, same2]
  exact valid

theorem generic_lookup10
    (sourceValue : Fin 277 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BigintCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BigintCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BigintCached.native.assigned (Airbender.Compiler.HelperValidityNative.BigintCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BigintCached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.genericExpressions10).Contains (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BigintCached.native.genericQueries.get ⟨10, by decide⟩
  have member := authored.1 query (List.get_mem Airbender.Compiler.LookupSourceNative.BigintCached.native.genericQueries ⟨10, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BigintCached.native.field10_0.source ∈ Airbender.Compiler.QueryFrameNative.BigintCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintCached.native.fields ⟨30, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BigintCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintCached.native.field10_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part1.generic_value10_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BigintCached.native.field10_1.source ∈ Airbender.Compiler.QueryFrameNative.BigintCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintCached.native.fields ⟨31, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BigintCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintCached.native.field10_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part1.generic_value10_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BigintCached.native.field10_2.source ∈ Airbender.Compiler.QueryFrameNative.BigintCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintCached.native.fields ⟨32, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BigintCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintCached.native.field10_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part1.generic_value10_2 physical data arithmetic).trans transported2
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BigintCached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BigintCached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Bigint" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.genericExpressions10, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BigintCached.native.model.Contains Airbender.Compiler.TableNative.BigintCached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part1.genericExpression10_0.eval (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part1.genericExpression10_1.eval (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part1.genericExpression10_2.eval (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data)]
  rw [same0, same1, same2]
  exact valid

theorem generic_lookup11
    (sourceValue : Fin 277 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BigintCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BigintCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BigintCached.native.assigned (Airbender.Compiler.HelperValidityNative.BigintCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BigintCached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.genericExpressions11).Contains (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BigintCached.native.genericQueries.get ⟨11, by decide⟩
  have member := authored.1 query (List.get_mem Airbender.Compiler.LookupSourceNative.BigintCached.native.genericQueries ⟨11, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BigintCached.native.field11_0.source ∈ Airbender.Compiler.QueryFrameNative.BigintCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintCached.native.fields ⟨33, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BigintCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintCached.native.field11_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part1.generic_value11_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BigintCached.native.field11_1.source ∈ Airbender.Compiler.QueryFrameNative.BigintCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintCached.native.fields ⟨34, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BigintCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintCached.native.field11_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part1.generic_value11_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BigintCached.native.field11_2.source ∈ Airbender.Compiler.QueryFrameNative.BigintCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintCached.native.fields ⟨35, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BigintCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintCached.native.field11_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part1.generic_value11_2 physical data arithmetic).trans transported2
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BigintCached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BigintCached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Bigint" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.genericExpressions11, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BigintCached.native.model.Contains Airbender.Compiler.TableNative.BigintCached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part1.genericExpression11_0.eval (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part1.genericExpression11_1.eval (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part1.genericExpression11_2.eval (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data)]
  rw [same0, same1, same2]
  exact valid

theorem generic_lookup12
    (sourceValue : Fin 277 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BigintCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BigintCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BigintCached.native.assigned (Airbender.Compiler.HelperValidityNative.BigintCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BigintCached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.genericExpressions12).Contains (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BigintCached.native.genericQueries.get ⟨12, by decide⟩
  have member := authored.1 query (List.get_mem Airbender.Compiler.LookupSourceNative.BigintCached.native.genericQueries ⟨12, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BigintCached.native.field12_0.source ∈ Airbender.Compiler.QueryFrameNative.BigintCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintCached.native.fields ⟨36, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BigintCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintCached.native.field12_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part1.generic_value12_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BigintCached.native.field12_1.source ∈ Airbender.Compiler.QueryFrameNative.BigintCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintCached.native.fields ⟨37, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BigintCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintCached.native.field12_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part1.generic_value12_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BigintCached.native.field12_2.source ∈ Airbender.Compiler.QueryFrameNative.BigintCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintCached.native.fields ⟨38, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BigintCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintCached.native.field12_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part1.generic_value12_2 physical data arithmetic).trans transported2
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BigintCached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BigintCached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Bigint" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.genericExpressions12, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BigintCached.native.model.Contains Airbender.Compiler.TableNative.BigintCached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part1.genericExpression12_0.eval (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part1.genericExpression12_1.eval (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part1.genericExpression12_2.eval (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data)]
  rw [same0, same1, same2]
  exact valid

theorem generic_lookup13
    (sourceValue : Fin 277 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BigintCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BigintCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BigintCached.native.assigned (Airbender.Compiler.HelperValidityNative.BigintCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BigintCached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.genericExpressions13).Contains (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BigintCached.native.genericQueries.get ⟨13, by decide⟩
  have member := authored.1 query (List.get_mem Airbender.Compiler.LookupSourceNative.BigintCached.native.genericQueries ⟨13, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BigintCached.native.field13_0.source ∈ Airbender.Compiler.QueryFrameNative.BigintCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintCached.native.fields ⟨39, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BigintCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintCached.native.field13_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part1.generic_value13_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BigintCached.native.field13_1.source ∈ Airbender.Compiler.QueryFrameNative.BigintCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintCached.native.fields ⟨40, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BigintCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintCached.native.field13_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part1.generic_value13_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BigintCached.native.field13_2.source ∈ Airbender.Compiler.QueryFrameNative.BigintCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintCached.native.fields ⟨41, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BigintCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintCached.native.field13_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part1.generic_value13_2 physical data arithmetic).trans transported2
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BigintCached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BigintCached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Bigint" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.genericExpressions13, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BigintCached.native.model.Contains Airbender.Compiler.TableNative.BigintCached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part1.genericExpression13_0.eval (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part1.genericExpression13_1.eval (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part1.genericExpression13_2.eval (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data)]
  rw [same0, same1, same2]
  exact valid

theorem generic_lookup14
    (sourceValue : Fin 277 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BigintCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BigintCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BigintCached.native.assigned (Airbender.Compiler.HelperValidityNative.BigintCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BigintCached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.genericExpressions14).Contains (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BigintCached.native.genericQueries.get ⟨14, by decide⟩
  have member := authored.1 query (List.get_mem Airbender.Compiler.LookupSourceNative.BigintCached.native.genericQueries ⟨14, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BigintCached.native.field14_0.source ∈ Airbender.Compiler.QueryFrameNative.BigintCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintCached.native.fields ⟨42, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BigintCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintCached.native.field14_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part1.generic_value14_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BigintCached.native.field14_1.source ∈ Airbender.Compiler.QueryFrameNative.BigintCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintCached.native.fields ⟨43, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BigintCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintCached.native.field14_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part1.generic_value14_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BigintCached.native.field14_2.source ∈ Airbender.Compiler.QueryFrameNative.BigintCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintCached.native.fields ⟨44, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BigintCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintCached.native.field14_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part1.generic_value14_2 physical data arithmetic).trans transported2
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BigintCached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BigintCached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Bigint" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.genericExpressions14, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BigintCached.native.model.Contains Airbender.Compiler.TableNative.BigintCached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part1.genericExpression14_0.eval (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part1.genericExpression14_1.eval (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part1.genericExpression14_2.eval (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data)]
  rw [same0, same1, same2]
  exact valid

theorem generic_lookup15
    (sourceValue : Fin 277 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BigintCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BigintCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BigintCached.native.assigned (Airbender.Compiler.HelperValidityNative.BigintCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BigintCached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.genericExpressions15).Contains (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BigintCached.native.genericQueries.get ⟨15, by decide⟩
  have member := authored.1 query (List.get_mem Airbender.Compiler.LookupSourceNative.BigintCached.native.genericQueries ⟨15, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BigintCached.native.field15_0.source ∈ Airbender.Compiler.QueryFrameNative.BigintCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintCached.native.fields ⟨45, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BigintCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintCached.native.field15_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part1.generic_value15_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BigintCached.native.field15_1.source ∈ Airbender.Compiler.QueryFrameNative.BigintCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintCached.native.fields ⟨46, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BigintCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintCached.native.field15_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part1.generic_value15_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BigintCached.native.field15_2.source ∈ Airbender.Compiler.QueryFrameNative.BigintCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintCached.native.fields ⟨47, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BigintCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintCached.native.field15_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part1.generic_value15_2 physical data arithmetic).trans transported2
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BigintCached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BigintCached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Bigint" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.genericExpressions15, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BigintCached.native.model.Contains Airbender.Compiler.TableNative.BigintCached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part1.genericExpression15_0.eval (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part1.genericExpression15_1.eval (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part1.genericExpression15_2.eval (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data)]
  rw [same0, same1, same2]
  exact valid


end Airbender.Compiler.CleanClosedNative.BigintCached
