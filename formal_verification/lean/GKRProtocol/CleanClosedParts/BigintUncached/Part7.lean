import GKRProtocol.CleanClosedParts.BigintUncached.Shared

namespace Airbender.Compiler.CleanClosedNative.BigintUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

theorem generic_lookup56
    (sourceValue : Fin 277 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BigintUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BigintUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BigintUncached.native.assigned (Airbender.Compiler.HelperValidityNative.BigintUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BigintUncached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.genericExpressions56).Contains (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BigintUncached.native.genericQueries.get ⟨56, by decide⟩
  have member := authored.1 query (List.get_mem Airbender.Compiler.LookupSourceNative.BigintUncached.native.genericQueries ⟨56, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BigintUncached.native.field56_0.source ∈ Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields ⟨168, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintUncached.native.field56_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part7.generic_value56_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BigintUncached.native.field56_1.source ∈ Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields ⟨169, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintUncached.native.field56_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part7.generic_value56_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BigintUncached.native.field56_2.source ∈ Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields ⟨170, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintUncached.native.field56_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part7.generic_value56_2 physical data arithmetic).trans transported2
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BigintUncached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BigintUncached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Bigint" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.genericExpressions56, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BigintUncached.native.model.Contains Airbender.Compiler.TableNative.BigintUncached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part7.genericExpression56_0.eval (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part7.genericExpression56_1.eval (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part7.genericExpression56_2.eval (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data)]
  rw [same0, same1, same2]
  exact valid

theorem generic_lookup57
    (sourceValue : Fin 277 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BigintUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BigintUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BigintUncached.native.assigned (Airbender.Compiler.HelperValidityNative.BigintUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BigintUncached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.genericExpressions57).Contains (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BigintUncached.native.genericQueries.get ⟨57, by decide⟩
  have member := authored.1 query (List.get_mem Airbender.Compiler.LookupSourceNative.BigintUncached.native.genericQueries ⟨57, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BigintUncached.native.field57_0.source ∈ Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields ⟨171, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintUncached.native.field57_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part7.generic_value57_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BigintUncached.native.field57_1.source ∈ Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields ⟨172, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintUncached.native.field57_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part7.generic_value57_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BigintUncached.native.field57_2.source ∈ Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields ⟨173, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintUncached.native.field57_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part7.generic_value57_2 physical data arithmetic).trans transported2
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BigintUncached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BigintUncached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Bigint" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.genericExpressions57, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BigintUncached.native.model.Contains Airbender.Compiler.TableNative.BigintUncached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part7.genericExpression57_0.eval (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part7.genericExpression57_1.eval (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part7.genericExpression57_2.eval (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data)]
  rw [same0, same1, same2]
  exact valid

theorem generic_lookup58
    (sourceValue : Fin 277 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BigintUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BigintUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BigintUncached.native.assigned (Airbender.Compiler.HelperValidityNative.BigintUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BigintUncached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.genericExpressions58).Contains (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BigintUncached.native.genericQueries.get ⟨58, by decide⟩
  have member := authored.1 query (List.get_mem Airbender.Compiler.LookupSourceNative.BigintUncached.native.genericQueries ⟨58, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BigintUncached.native.field58_0.source ∈ Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields ⟨174, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintUncached.native.field58_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part7.generic_value58_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BigintUncached.native.field58_1.source ∈ Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields ⟨175, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintUncached.native.field58_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part7.generic_value58_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BigintUncached.native.field58_2.source ∈ Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields ⟨176, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintUncached.native.field58_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part7.generic_value58_2 physical data arithmetic).trans transported2
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BigintUncached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BigintUncached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Bigint" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.genericExpressions58, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BigintUncached.native.model.Contains Airbender.Compiler.TableNative.BigintUncached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part7.genericExpression58_0.eval (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part7.genericExpression58_1.eval (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part7.genericExpression58_2.eval (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data)]
  rw [same0, same1, same2]
  exact valid

theorem generic_lookup59
    (sourceValue : Fin 277 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BigintUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BigintUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BigintUncached.native.assigned (Airbender.Compiler.HelperValidityNative.BigintUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BigintUncached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.genericExpressions59).Contains (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BigintUncached.native.genericQueries.get ⟨59, by decide⟩
  have member := authored.1 query (List.get_mem Airbender.Compiler.LookupSourceNative.BigintUncached.native.genericQueries ⟨59, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BigintUncached.native.field59_0.source ∈ Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields ⟨177, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintUncached.native.field59_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part7.generic_value59_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BigintUncached.native.field59_1.source ∈ Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields ⟨178, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintUncached.native.field59_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part7.generic_value59_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BigintUncached.native.field59_2.source ∈ Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields ⟨179, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintUncached.native.field59_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part7.generic_value59_2 physical data arithmetic).trans transported2
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BigintUncached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BigintUncached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Bigint" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.genericExpressions59, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BigintUncached.native.model.Contains Airbender.Compiler.TableNative.BigintUncached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part7.genericExpression59_0.eval (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part7.genericExpression59_1.eval (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part7.genericExpression59_2.eval (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data)]
  rw [same0, same1, same2]
  exact valid

theorem generic_lookup60
    (sourceValue : Fin 277 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BigintUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BigintUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BigintUncached.native.assigned (Airbender.Compiler.HelperValidityNative.BigintUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BigintUncached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.genericExpressions60).Contains (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BigintUncached.native.genericQueries.get ⟨60, by decide⟩
  have member := authored.1 query (List.get_mem Airbender.Compiler.LookupSourceNative.BigintUncached.native.genericQueries ⟨60, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BigintUncached.native.field60_0.source ∈ Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields ⟨180, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintUncached.native.field60_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part7.generic_value60_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BigintUncached.native.field60_1.source ∈ Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields ⟨181, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintUncached.native.field60_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part7.generic_value60_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BigintUncached.native.field60_2.source ∈ Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields ⟨182, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintUncached.native.field60_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part7.generic_value60_2 physical data arithmetic).trans transported2
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BigintUncached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BigintUncached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Bigint" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.genericExpressions60, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BigintUncached.native.model.Contains Airbender.Compiler.TableNative.BigintUncached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part7.genericExpression60_0.eval (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part7.genericExpression60_1.eval (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part7.genericExpression60_2.eval (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data)]
  rw [same0, same1, same2]
  exact valid


end Airbender.Compiler.CleanClosedNative.BigintUncached
