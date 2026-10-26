import Airbender.Proofs.GKRProtocol.CleanClosedParts.BigintCached.Shared

namespace Airbender.Compiler.CleanClosedNative.BigintCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

theorem generic_lookup48
    (sourceValue : Fin 277 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BigintCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BigintCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BigintCached.native.assigned (Airbender.Compiler.HelperValidityNative.BigintCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BigintCached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.genericExpressions48).Contains (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BigintCached.native.genericQueries.get ⟨48, by decide⟩
  have member := authored.1 query (List.get_mem Airbender.Compiler.LookupSourceNative.BigintCached.native.genericQueries ⟨48, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BigintCached.native.field48_0.source ∈ Airbender.Compiler.QueryFrameNative.BigintCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintCached.native.fields ⟨144, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BigintCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintCached.native.field48_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part6.generic_value48_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BigintCached.native.field48_1.source ∈ Airbender.Compiler.QueryFrameNative.BigintCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintCached.native.fields ⟨145, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BigintCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintCached.native.field48_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part6.generic_value48_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BigintCached.native.field48_2.source ∈ Airbender.Compiler.QueryFrameNative.BigintCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintCached.native.fields ⟨146, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BigintCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintCached.native.field48_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part6.generic_value48_2 physical data arithmetic).trans transported2
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BigintCached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BigintCached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Bigint" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.genericExpressions48, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BigintCached.native.model.Contains Airbender.Compiler.TableNative.BigintCached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part6.genericExpression48_0.eval (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part6.genericExpression48_1.eval (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part6.genericExpression48_2.eval (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data)]
  rw [same0, same1, same2]
  exact valid

theorem generic_lookup49
    (sourceValue : Fin 277 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BigintCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BigintCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BigintCached.native.assigned (Airbender.Compiler.HelperValidityNative.BigintCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BigintCached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.genericExpressions49).Contains (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BigintCached.native.genericQueries.get ⟨49, by decide⟩
  have member := authored.1 query (List.get_mem Airbender.Compiler.LookupSourceNative.BigintCached.native.genericQueries ⟨49, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BigintCached.native.field49_0.source ∈ Airbender.Compiler.QueryFrameNative.BigintCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintCached.native.fields ⟨147, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BigintCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintCached.native.field49_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part6.generic_value49_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BigintCached.native.field49_1.source ∈ Airbender.Compiler.QueryFrameNative.BigintCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintCached.native.fields ⟨148, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BigintCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintCached.native.field49_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part6.generic_value49_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BigintCached.native.field49_2.source ∈ Airbender.Compiler.QueryFrameNative.BigintCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintCached.native.fields ⟨149, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BigintCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintCached.native.field49_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part6.generic_value49_2 physical data arithmetic).trans transported2
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BigintCached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BigintCached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Bigint" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.genericExpressions49, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BigintCached.native.model.Contains Airbender.Compiler.TableNative.BigintCached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part6.genericExpression49_0.eval (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part6.genericExpression49_1.eval (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part6.genericExpression49_2.eval (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data)]
  rw [same0, same1, same2]
  exact valid

theorem generic_lookup50
    (sourceValue : Fin 277 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BigintCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BigintCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BigintCached.native.assigned (Airbender.Compiler.HelperValidityNative.BigintCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BigintCached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.genericExpressions50).Contains (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BigintCached.native.genericQueries.get ⟨50, by decide⟩
  have member := authored.1 query (List.get_mem Airbender.Compiler.LookupSourceNative.BigintCached.native.genericQueries ⟨50, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BigintCached.native.field50_0.source ∈ Airbender.Compiler.QueryFrameNative.BigintCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintCached.native.fields ⟨150, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BigintCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintCached.native.field50_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part6.generic_value50_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BigintCached.native.field50_1.source ∈ Airbender.Compiler.QueryFrameNative.BigintCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintCached.native.fields ⟨151, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BigintCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintCached.native.field50_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part6.generic_value50_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BigintCached.native.field50_2.source ∈ Airbender.Compiler.QueryFrameNative.BigintCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintCached.native.fields ⟨152, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BigintCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintCached.native.field50_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part6.generic_value50_2 physical data arithmetic).trans transported2
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BigintCached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BigintCached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Bigint" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.genericExpressions50, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BigintCached.native.model.Contains Airbender.Compiler.TableNative.BigintCached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part6.genericExpression50_0.eval (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part6.genericExpression50_1.eval (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part6.genericExpression50_2.eval (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data)]
  rw [same0, same1, same2]
  exact valid

theorem generic_lookup51
    (sourceValue : Fin 277 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BigintCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BigintCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BigintCached.native.assigned (Airbender.Compiler.HelperValidityNative.BigintCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BigintCached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.genericExpressions51).Contains (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BigintCached.native.genericQueries.get ⟨51, by decide⟩
  have member := authored.1 query (List.get_mem Airbender.Compiler.LookupSourceNative.BigintCached.native.genericQueries ⟨51, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BigintCached.native.field51_0.source ∈ Airbender.Compiler.QueryFrameNative.BigintCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintCached.native.fields ⟨153, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BigintCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintCached.native.field51_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part6.generic_value51_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BigintCached.native.field51_1.source ∈ Airbender.Compiler.QueryFrameNative.BigintCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintCached.native.fields ⟨154, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BigintCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintCached.native.field51_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part6.generic_value51_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BigintCached.native.field51_2.source ∈ Airbender.Compiler.QueryFrameNative.BigintCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintCached.native.fields ⟨155, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BigintCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintCached.native.field51_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part6.generic_value51_2 physical data arithmetic).trans transported2
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BigintCached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BigintCached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Bigint" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.genericExpressions51, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BigintCached.native.model.Contains Airbender.Compiler.TableNative.BigintCached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part6.genericExpression51_0.eval (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part6.genericExpression51_1.eval (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part6.genericExpression51_2.eval (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data)]
  rw [same0, same1, same2]
  exact valid

theorem generic_lookup52
    (sourceValue : Fin 277 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BigintCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BigintCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BigintCached.native.assigned (Airbender.Compiler.HelperValidityNative.BigintCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BigintCached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.genericExpressions52).Contains (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BigintCached.native.genericQueries.get ⟨52, by decide⟩
  have member := authored.1 query (List.get_mem Airbender.Compiler.LookupSourceNative.BigintCached.native.genericQueries ⟨52, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BigintCached.native.field52_0.source ∈ Airbender.Compiler.QueryFrameNative.BigintCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintCached.native.fields ⟨156, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BigintCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintCached.native.field52_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part6.generic_value52_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BigintCached.native.field52_1.source ∈ Airbender.Compiler.QueryFrameNative.BigintCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintCached.native.fields ⟨157, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BigintCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintCached.native.field52_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part6.generic_value52_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BigintCached.native.field52_2.source ∈ Airbender.Compiler.QueryFrameNative.BigintCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintCached.native.fields ⟨158, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BigintCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintCached.native.field52_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part6.generic_value52_2 physical data arithmetic).trans transported2
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BigintCached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BigintCached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Bigint" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.genericExpressions52, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BigintCached.native.model.Contains Airbender.Compiler.TableNative.BigintCached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part6.genericExpression52_0.eval (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part6.genericExpression52_1.eval (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part6.genericExpression52_2.eval (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data)]
  rw [same0, same1, same2]
  exact valid

theorem generic_lookup53
    (sourceValue : Fin 277 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BigintCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BigintCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BigintCached.native.assigned (Airbender.Compiler.HelperValidityNative.BigintCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BigintCached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.genericExpressions53).Contains (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BigintCached.native.genericQueries.get ⟨53, by decide⟩
  have member := authored.1 query (List.get_mem Airbender.Compiler.LookupSourceNative.BigintCached.native.genericQueries ⟨53, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BigintCached.native.field53_0.source ∈ Airbender.Compiler.QueryFrameNative.BigintCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintCached.native.fields ⟨159, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BigintCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintCached.native.field53_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part6.generic_value53_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BigintCached.native.field53_1.source ∈ Airbender.Compiler.QueryFrameNative.BigintCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintCached.native.fields ⟨160, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BigintCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintCached.native.field53_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part6.generic_value53_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BigintCached.native.field53_2.source ∈ Airbender.Compiler.QueryFrameNative.BigintCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintCached.native.fields ⟨161, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BigintCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintCached.native.field53_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part6.generic_value53_2 physical data arithmetic).trans transported2
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BigintCached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BigintCached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Bigint" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.genericExpressions53, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BigintCached.native.model.Contains Airbender.Compiler.TableNative.BigintCached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part6.genericExpression53_0.eval (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part6.genericExpression53_1.eval (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part6.genericExpression53_2.eval (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data)]
  rw [same0, same1, same2]
  exact valid

theorem generic_lookup54
    (sourceValue : Fin 277 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BigintCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BigintCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BigintCached.native.assigned (Airbender.Compiler.HelperValidityNative.BigintCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BigintCached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.genericExpressions54).Contains (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BigintCached.native.genericQueries.get ⟨54, by decide⟩
  have member := authored.1 query (List.get_mem Airbender.Compiler.LookupSourceNative.BigintCached.native.genericQueries ⟨54, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BigintCached.native.field54_0.source ∈ Airbender.Compiler.QueryFrameNative.BigintCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintCached.native.fields ⟨162, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BigintCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintCached.native.field54_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part6.generic_value54_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BigintCached.native.field54_1.source ∈ Airbender.Compiler.QueryFrameNative.BigintCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintCached.native.fields ⟨163, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BigintCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintCached.native.field54_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part6.generic_value54_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BigintCached.native.field54_2.source ∈ Airbender.Compiler.QueryFrameNative.BigintCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintCached.native.fields ⟨164, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BigintCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintCached.native.field54_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part6.generic_value54_2 physical data arithmetic).trans transported2
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BigintCached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BigintCached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Bigint" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.genericExpressions54, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BigintCached.native.model.Contains Airbender.Compiler.TableNative.BigintCached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part6.genericExpression54_0.eval (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part6.genericExpression54_1.eval (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part6.genericExpression54_2.eval (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data)]
  rw [same0, same1, same2]
  exact valid

theorem generic_lookup55
    (sourceValue : Fin 277 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BigintCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BigintCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BigintCached.native.assigned (Airbender.Compiler.HelperValidityNative.BigintCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BigintCached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.genericExpressions55).Contains (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BigintCached.native.genericQueries.get ⟨55, by decide⟩
  have member := authored.1 query (List.get_mem Airbender.Compiler.LookupSourceNative.BigintCached.native.genericQueries ⟨55, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BigintCached.native.field55_0.source ∈ Airbender.Compiler.QueryFrameNative.BigintCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintCached.native.fields ⟨165, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BigintCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintCached.native.field55_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part6.generic_value55_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BigintCached.native.field55_1.source ∈ Airbender.Compiler.QueryFrameNative.BigintCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintCached.native.fields ⟨166, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BigintCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintCached.native.field55_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part6.generic_value55_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BigintCached.native.field55_2.source ∈ Airbender.Compiler.QueryFrameNative.BigintCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintCached.native.fields ⟨167, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BigintCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintCached.native.field55_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part6.generic_value55_2 physical data arithmetic).trans transported2
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BigintCached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BigintCached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Bigint" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.genericExpressions55, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BigintCached.native.model.Contains Airbender.Compiler.TableNative.BigintCached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part6.genericExpression55_0.eval (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part6.genericExpression55_1.eval (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.part6.genericExpression55_2.eval (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical data)]
  rw [same0, same1, same2]
  exact valid


end Airbender.Compiler.CleanClosedNative.BigintCached
