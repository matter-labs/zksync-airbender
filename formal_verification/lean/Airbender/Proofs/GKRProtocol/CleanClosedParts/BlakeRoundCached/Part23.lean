import Airbender.Proofs.GKRProtocol.CleanClosedParts.BlakeRoundCached.Shared

namespace Airbender.Compiler.CleanClosedNative.BlakeRoundCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

theorem generic_lookup184
    (sourceValue : Fin 763 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BlakeRoundCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BlakeRoundCached.native.assigned (Airbender.Compiler.HelperValidityNative.BlakeRoundCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BlakeRoundCached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.genericExpressions184).Contains (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BlakeRoundCached.native.genericQueries.get ⟨184, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.BlakeRoundCached.native.genericQueries ⟨184, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field184_0.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨1104, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field184_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part23.generic_value184_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field184_1.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨1105, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field184_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part23.generic_value184_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field184_2.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨1106, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field184_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part23.generic_value184_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field184_3.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨1107, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field184_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part23.generic_value184_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field184_4.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨1108, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field184_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part23.generic_value184_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field184_5.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨1109, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field184_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part23.generic_value184_5 physical data arithmetic).trans transported5
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BlakeRoundCached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BlakeRoundCached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Blake2Round" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.genericExpressions184, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BlakeRoundCached.native.model.Contains Airbender.Compiler.TableNative.BlakeRoundCached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part23.genericExpression184_0.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part23.genericExpression184_1.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part23.genericExpression184_2.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part23.genericExpression184_3.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part23.genericExpression184_4.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part23.genericExpression184_5.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5]
  exact valid

theorem generic_lookup185
    (sourceValue : Fin 763 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BlakeRoundCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BlakeRoundCached.native.assigned (Airbender.Compiler.HelperValidityNative.BlakeRoundCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BlakeRoundCached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.genericExpressions185).Contains (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BlakeRoundCached.native.genericQueries.get ⟨185, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.BlakeRoundCached.native.genericQueries ⟨185, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field185_0.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨1110, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field185_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part23.generic_value185_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field185_1.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨1111, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field185_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part23.generic_value185_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field185_2.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨1112, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field185_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part23.generic_value185_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field185_3.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨1113, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field185_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part23.generic_value185_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field185_4.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨1114, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field185_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part23.generic_value185_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field185_5.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨1115, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field185_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part23.generic_value185_5 physical data arithmetic).trans transported5
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BlakeRoundCached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BlakeRoundCached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Blake2Round" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.genericExpressions185, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BlakeRoundCached.native.model.Contains Airbender.Compiler.TableNative.BlakeRoundCached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part23.genericExpression185_0.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part23.genericExpression185_1.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part23.genericExpression185_2.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part23.genericExpression185_3.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part23.genericExpression185_4.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part23.genericExpression185_5.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5]
  exact valid

theorem generic_lookup186
    (sourceValue : Fin 763 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BlakeRoundCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BlakeRoundCached.native.assigned (Airbender.Compiler.HelperValidityNative.BlakeRoundCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BlakeRoundCached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.genericExpressions186).Contains (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BlakeRoundCached.native.genericQueries.get ⟨186, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.BlakeRoundCached.native.genericQueries ⟨186, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field186_0.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨1116, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field186_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part23.generic_value186_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field186_1.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨1117, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field186_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part23.generic_value186_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field186_2.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨1118, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field186_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part23.generic_value186_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field186_3.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨1119, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field186_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part23.generic_value186_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field186_4.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨1120, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field186_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part23.generic_value186_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field186_5.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨1121, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field186_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part23.generic_value186_5 physical data arithmetic).trans transported5
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BlakeRoundCached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BlakeRoundCached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Blake2Round" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.genericExpressions186, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BlakeRoundCached.native.model.Contains Airbender.Compiler.TableNative.BlakeRoundCached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part23.genericExpression186_0.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part23.genericExpression186_1.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part23.genericExpression186_2.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part23.genericExpression186_3.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part23.genericExpression186_4.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part23.genericExpression186_5.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5]
  exact valid

theorem generic_lookup187
    (sourceValue : Fin 763 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BlakeRoundCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BlakeRoundCached.native.assigned (Airbender.Compiler.HelperValidityNative.BlakeRoundCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BlakeRoundCached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.genericExpressions187).Contains (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BlakeRoundCached.native.genericQueries.get ⟨187, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.BlakeRoundCached.native.genericQueries ⟨187, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field187_0.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨1122, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field187_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part23.generic_value187_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field187_1.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨1123, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field187_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part23.generic_value187_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field187_2.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨1124, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field187_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part23.generic_value187_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field187_3.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨1125, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field187_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part23.generic_value187_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field187_4.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨1126, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field187_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part23.generic_value187_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field187_5.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨1127, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field187_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part23.generic_value187_5 physical data arithmetic).trans transported5
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BlakeRoundCached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BlakeRoundCached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Blake2Round" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.genericExpressions187, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BlakeRoundCached.native.model.Contains Airbender.Compiler.TableNative.BlakeRoundCached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part23.genericExpression187_0.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part23.genericExpression187_1.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part23.genericExpression187_2.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part23.genericExpression187_3.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part23.genericExpression187_4.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part23.genericExpression187_5.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5]
  exact valid

theorem generic_lookup188
    (sourceValue : Fin 763 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BlakeRoundCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BlakeRoundCached.native.assigned (Airbender.Compiler.HelperValidityNative.BlakeRoundCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BlakeRoundCached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.genericExpressions188).Contains (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BlakeRoundCached.native.genericQueries.get ⟨188, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.BlakeRoundCached.native.genericQueries ⟨188, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field188_0.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨1128, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field188_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part23.generic_value188_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field188_1.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨1129, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field188_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part23.generic_value188_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field188_2.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨1130, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field188_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part23.generic_value188_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field188_3.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨1131, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field188_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part23.generic_value188_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field188_4.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨1132, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field188_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part23.generic_value188_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field188_5.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨1133, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field188_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part23.generic_value188_5 physical data arithmetic).trans transported5
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BlakeRoundCached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BlakeRoundCached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Blake2Round" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.genericExpressions188, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BlakeRoundCached.native.model.Contains Airbender.Compiler.TableNative.BlakeRoundCached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part23.genericExpression188_0.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part23.genericExpression188_1.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part23.genericExpression188_2.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part23.genericExpression188_3.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part23.genericExpression188_4.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part23.genericExpression188_5.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5]
  exact valid

theorem generic_lookup189
    (sourceValue : Fin 763 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BlakeRoundCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BlakeRoundCached.native.assigned (Airbender.Compiler.HelperValidityNative.BlakeRoundCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BlakeRoundCached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.genericExpressions189).Contains (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BlakeRoundCached.native.genericQueries.get ⟨189, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.BlakeRoundCached.native.genericQueries ⟨189, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field189_0.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨1134, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field189_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part23.generic_value189_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field189_1.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨1135, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field189_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part23.generic_value189_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field189_2.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨1136, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field189_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part23.generic_value189_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field189_3.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨1137, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field189_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part23.generic_value189_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field189_4.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨1138, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field189_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part23.generic_value189_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field189_5.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨1139, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field189_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part23.generic_value189_5 physical data arithmetic).trans transported5
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BlakeRoundCached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BlakeRoundCached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Blake2Round" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.genericExpressions189, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BlakeRoundCached.native.model.Contains Airbender.Compiler.TableNative.BlakeRoundCached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part23.genericExpression189_0.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part23.genericExpression189_1.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part23.genericExpression189_2.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part23.genericExpression189_3.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part23.genericExpression189_4.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part23.genericExpression189_5.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5]
  exact valid

theorem generic_lookup190
    (sourceValue : Fin 763 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BlakeRoundCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BlakeRoundCached.native.assigned (Airbender.Compiler.HelperValidityNative.BlakeRoundCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BlakeRoundCached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.genericExpressions190).Contains (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BlakeRoundCached.native.genericQueries.get ⟨190, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.BlakeRoundCached.native.genericQueries ⟨190, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field190_0.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨1140, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field190_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part23.generic_value190_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field190_1.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨1141, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field190_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part23.generic_value190_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field190_2.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨1142, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field190_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part23.generic_value190_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field190_3.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨1143, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field190_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part23.generic_value190_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field190_4.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨1144, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field190_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part23.generic_value190_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field190_5.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨1145, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field190_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part23.generic_value190_5 physical data arithmetic).trans transported5
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BlakeRoundCached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BlakeRoundCached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Blake2Round" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.genericExpressions190, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BlakeRoundCached.native.model.Contains Airbender.Compiler.TableNative.BlakeRoundCached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part23.genericExpression190_0.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part23.genericExpression190_1.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part23.genericExpression190_2.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part23.genericExpression190_3.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part23.genericExpression190_4.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part23.genericExpression190_5.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5]
  exact valid

theorem generic_lookup191
    (sourceValue : Fin 763 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BlakeRoundCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BlakeRoundCached.native.assigned (Airbender.Compiler.HelperValidityNative.BlakeRoundCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BlakeRoundCached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.genericExpressions191).Contains (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BlakeRoundCached.native.genericQueries.get ⟨191, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.BlakeRoundCached.native.genericQueries ⟨191, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field191_0.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨1146, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field191_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part23.generic_value191_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field191_1.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨1147, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field191_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part23.generic_value191_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field191_2.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨1148, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field191_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part23.generic_value191_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field191_3.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨1149, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field191_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part23.generic_value191_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field191_4.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨1150, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field191_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part23.generic_value191_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field191_5.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨1151, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field191_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part23.generic_value191_5 physical data arithmetic).trans transported5
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BlakeRoundCached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BlakeRoundCached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Blake2Round" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.genericExpressions191, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BlakeRoundCached.native.model.Contains Airbender.Compiler.TableNative.BlakeRoundCached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part23.genericExpression191_0.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part23.genericExpression191_1.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part23.genericExpression191_2.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part23.genericExpression191_3.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part23.genericExpression191_4.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part23.genericExpression191_5.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5]
  exact valid


end Airbender.Compiler.CleanClosedNative.BlakeRoundCached
