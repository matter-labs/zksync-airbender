import Airbender.Proofs.GKRProtocol.CleanClosedParts.BigintUncached.Shared

namespace Airbender.Compiler.CleanClosedNative.BigintUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

theorem generic_lookup24
    (sourceValue : Fin 277 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BigintUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BigintUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BigintUncached.native.assigned (Airbender.Compiler.HelperValidityNative.BigintUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BigintUncached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.genericExpressions24).Contains (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BigintUncached.native.genericQueries.get ⟨24, by decide⟩
  have member := authored.1 query (List.get_mem Airbender.Compiler.LookupSourceNative.BigintUncached.native.genericQueries ⟨24, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BigintUncached.native.field24_0.source ∈ Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields ⟨72, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintUncached.native.field24_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.generic_value24_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BigintUncached.native.field24_1.source ∈ Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields ⟨73, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintUncached.native.field24_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.generic_value24_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BigintUncached.native.field24_2.source ∈ Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields ⟨74, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintUncached.native.field24_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.generic_value24_2 physical data arithmetic).trans transported2
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BigintUncached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BigintUncached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Bigint" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.genericExpressions24, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BigintUncached.native.model.Contains Airbender.Compiler.TableNative.BigintUncached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.genericExpression24_0.eval (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.genericExpression24_1.eval (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.genericExpression24_2.eval (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data)]
  rw [same0, same1, same2]
  exact valid

theorem generic_lookup25
    (sourceValue : Fin 277 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BigintUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BigintUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BigintUncached.native.assigned (Airbender.Compiler.HelperValidityNative.BigintUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BigintUncached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.genericExpressions25).Contains (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BigintUncached.native.genericQueries.get ⟨25, by decide⟩
  have member := authored.1 query (List.get_mem Airbender.Compiler.LookupSourceNative.BigintUncached.native.genericQueries ⟨25, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BigintUncached.native.field25_0.source ∈ Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields ⟨75, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintUncached.native.field25_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.generic_value25_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BigintUncached.native.field25_1.source ∈ Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields ⟨76, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintUncached.native.field25_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.generic_value25_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BigintUncached.native.field25_2.source ∈ Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields ⟨77, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintUncached.native.field25_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.generic_value25_2 physical data arithmetic).trans transported2
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BigintUncached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BigintUncached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Bigint" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.genericExpressions25, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BigintUncached.native.model.Contains Airbender.Compiler.TableNative.BigintUncached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.genericExpression25_0.eval (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.genericExpression25_1.eval (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.genericExpression25_2.eval (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data)]
  rw [same0, same1, same2]
  exact valid

theorem generic_lookup26
    (sourceValue : Fin 277 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BigintUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BigintUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BigintUncached.native.assigned (Airbender.Compiler.HelperValidityNative.BigintUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BigintUncached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.genericExpressions26).Contains (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BigintUncached.native.genericQueries.get ⟨26, by decide⟩
  have member := authored.1 query (List.get_mem Airbender.Compiler.LookupSourceNative.BigintUncached.native.genericQueries ⟨26, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BigintUncached.native.field26_0.source ∈ Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields ⟨78, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintUncached.native.field26_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.generic_value26_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BigintUncached.native.field26_1.source ∈ Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields ⟨79, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintUncached.native.field26_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.generic_value26_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BigintUncached.native.field26_2.source ∈ Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields ⟨80, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintUncached.native.field26_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.generic_value26_2 physical data arithmetic).trans transported2
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BigintUncached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BigintUncached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Bigint" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.genericExpressions26, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BigintUncached.native.model.Contains Airbender.Compiler.TableNative.BigintUncached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.genericExpression26_0.eval (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.genericExpression26_1.eval (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.genericExpression26_2.eval (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data)]
  rw [same0, same1, same2]
  exact valid

theorem generic_lookup27
    (sourceValue : Fin 277 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BigintUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BigintUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BigintUncached.native.assigned (Airbender.Compiler.HelperValidityNative.BigintUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BigintUncached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.genericExpressions27).Contains (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BigintUncached.native.genericQueries.get ⟨27, by decide⟩
  have member := authored.1 query (List.get_mem Airbender.Compiler.LookupSourceNative.BigintUncached.native.genericQueries ⟨27, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BigintUncached.native.field27_0.source ∈ Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields ⟨81, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintUncached.native.field27_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.generic_value27_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BigintUncached.native.field27_1.source ∈ Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields ⟨82, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintUncached.native.field27_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.generic_value27_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BigintUncached.native.field27_2.source ∈ Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields ⟨83, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintUncached.native.field27_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.generic_value27_2 physical data arithmetic).trans transported2
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BigintUncached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BigintUncached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Bigint" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.genericExpressions27, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BigintUncached.native.model.Contains Airbender.Compiler.TableNative.BigintUncached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.genericExpression27_0.eval (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.genericExpression27_1.eval (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.genericExpression27_2.eval (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data)]
  rw [same0, same1, same2]
  exact valid

theorem generic_lookup28
    (sourceValue : Fin 277 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BigintUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BigintUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BigintUncached.native.assigned (Airbender.Compiler.HelperValidityNative.BigintUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BigintUncached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.genericExpressions28).Contains (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BigintUncached.native.genericQueries.get ⟨28, by decide⟩
  have member := authored.1 query (List.get_mem Airbender.Compiler.LookupSourceNative.BigintUncached.native.genericQueries ⟨28, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BigintUncached.native.field28_0.source ∈ Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields ⟨84, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintUncached.native.field28_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.generic_value28_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BigintUncached.native.field28_1.source ∈ Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields ⟨85, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintUncached.native.field28_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.generic_value28_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BigintUncached.native.field28_2.source ∈ Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields ⟨86, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintUncached.native.field28_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.generic_value28_2 physical data arithmetic).trans transported2
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BigintUncached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BigintUncached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Bigint" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.genericExpressions28, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BigintUncached.native.model.Contains Airbender.Compiler.TableNative.BigintUncached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.genericExpression28_0.eval (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.genericExpression28_1.eval (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.genericExpression28_2.eval (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data)]
  rw [same0, same1, same2]
  exact valid

theorem generic_lookup29
    (sourceValue : Fin 277 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BigintUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BigintUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BigintUncached.native.assigned (Airbender.Compiler.HelperValidityNative.BigintUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BigintUncached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.genericExpressions29).Contains (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BigintUncached.native.genericQueries.get ⟨29, by decide⟩
  have member := authored.1 query (List.get_mem Airbender.Compiler.LookupSourceNative.BigintUncached.native.genericQueries ⟨29, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BigintUncached.native.field29_0.source ∈ Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields ⟨87, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintUncached.native.field29_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.generic_value29_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BigintUncached.native.field29_1.source ∈ Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields ⟨88, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintUncached.native.field29_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.generic_value29_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BigintUncached.native.field29_2.source ∈ Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields ⟨89, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintUncached.native.field29_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.generic_value29_2 physical data arithmetic).trans transported2
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BigintUncached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BigintUncached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Bigint" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.genericExpressions29, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BigintUncached.native.model.Contains Airbender.Compiler.TableNative.BigintUncached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.genericExpression29_0.eval (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.genericExpression29_1.eval (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.genericExpression29_2.eval (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data)]
  rw [same0, same1, same2]
  exact valid

theorem generic_lookup30
    (sourceValue : Fin 277 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BigintUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BigintUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BigintUncached.native.assigned (Airbender.Compiler.HelperValidityNative.BigintUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BigintUncached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.genericExpressions30).Contains (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BigintUncached.native.genericQueries.get ⟨30, by decide⟩
  have member := authored.1 query (List.get_mem Airbender.Compiler.LookupSourceNative.BigintUncached.native.genericQueries ⟨30, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BigintUncached.native.field30_0.source ∈ Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields ⟨90, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintUncached.native.field30_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.generic_value30_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BigintUncached.native.field30_1.source ∈ Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields ⟨91, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintUncached.native.field30_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.generic_value30_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BigintUncached.native.field30_2.source ∈ Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields ⟨92, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintUncached.native.field30_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.generic_value30_2 physical data arithmetic).trans transported2
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BigintUncached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BigintUncached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Bigint" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.genericExpressions30, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BigintUncached.native.model.Contains Airbender.Compiler.TableNative.BigintUncached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.genericExpression30_0.eval (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.genericExpression30_1.eval (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.genericExpression30_2.eval (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data)]
  rw [same0, same1, same2]
  exact valid

theorem generic_lookup31
    (sourceValue : Fin 277 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BigintUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BigintUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BigintUncached.native.assigned (Airbender.Compiler.HelperValidityNative.BigintUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BigintUncached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.genericExpressions31).Contains (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BigintUncached.native.genericQueries.get ⟨31, by decide⟩
  have member := authored.1 query (List.get_mem Airbender.Compiler.LookupSourceNative.BigintUncached.native.genericQueries ⟨31, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BigintUncached.native.field31_0.source ∈ Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields ⟨93, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintUncached.native.field31_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.generic_value31_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BigintUncached.native.field31_1.source ∈ Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields ⟨94, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintUncached.native.field31_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.generic_value31_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BigintUncached.native.field31_2.source ∈ Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields ⟨95, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintUncached.native.field31_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.generic_value31_2 physical data arithmetic).trans transported2
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BigintUncached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BigintUncached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Bigint" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.genericExpressions31, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BigintUncached.native.model.Contains Airbender.Compiler.TableNative.BigintUncached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.genericExpression31_0.eval (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.genericExpression31_1.eval (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.genericExpression31_2.eval (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data)]
  rw [same0, same1, same2]
  exact valid


end Airbender.Compiler.CleanClosedNative.BigintUncached
