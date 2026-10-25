import GKRProtocol.CleanArgumentsNative.AddSubCached
import GKRProtocol.CleanScalarNative.AddSubCached
import GKRProtocol.CleanPrimitiveLookups
import GKRProtocol.CleanLinksNative.AddSubCached
import GKRProtocol.MaterializedWitnessNative.AddSubCached

namespace Airbender.Compiler.CleanClosedNative.AddSubCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

theorem clock_lookup_inventory :
    FlatOperation.lookups (Airbender.AddSub.clockConstraints (p := babyBearModulus)) =
    (Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.rangeExpressions.map Verification.range16) ++
    (Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.timestampExpressions.map Trace.timestampLookup) := by rfl

theorem range_lookup0
    (sourceValue : Fin 48 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.AddSubCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.AddSubCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.AddSubCached.native.assigned (Airbender.Compiler.HelperValidityNative.AddSubCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.AddSubCached.AuthoredLookupValid sourceValue) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.rangeExpression0).Contains (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.AddSubCached.native.range16Queries.get ⟨0, by decide⟩
  have member := authored.2 query (List.get_mem Airbender.Compiler.LookupSourceNative.AddSubCached.native.range16Queries ⟨0, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.AddSubCached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.AddSubCached.native.field0_0.source.value (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.originalProjection)] := member nonzero
  have present : Airbender.Compiler.LookupNative.AddSubCached.native.field0_0.source ∈ Airbender.Compiler.QueryFrameNative.AddSubCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.AddSubCached.native.fields ⟨9, by decide⟩
  have transported := Airbender.Compiler.QueryFrameNative.AddSubCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.AddSubCached.native.field0_0.source present
  have same := (Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.range_value0 physical data arithmetic).trans transported
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.AddSubCached.native.range16_clean_refinement _ valid _

theorem range_lookup1
    (sourceValue : Fin 48 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.AddSubCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.AddSubCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.AddSubCached.native.assigned (Airbender.Compiler.HelperValidityNative.AddSubCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.AddSubCached.AuthoredLookupValid sourceValue) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.rangeExpression1).Contains (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.AddSubCached.native.range16Queries.get ⟨1, by decide⟩
  have member := authored.2 query (List.get_mem Airbender.Compiler.LookupSourceNative.AddSubCached.native.range16Queries ⟨1, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.AddSubCached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.AddSubCached.native.field1_0.source.value (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.originalProjection)] := member nonzero
  have present : Airbender.Compiler.LookupNative.AddSubCached.native.field1_0.source ∈ Airbender.Compiler.QueryFrameNative.AddSubCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.AddSubCached.native.fields ⟨10, by decide⟩
  have transported := Airbender.Compiler.QueryFrameNative.AddSubCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.AddSubCached.native.field1_0.source present
  have same := (Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.range_value1 physical data arithmetic).trans transported
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.AddSubCached.native.range16_clean_refinement _ valid _

theorem range_lookup2
    (sourceValue : Fin 48 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.AddSubCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.AddSubCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.AddSubCached.native.assigned (Airbender.Compiler.HelperValidityNative.AddSubCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.AddSubCached.AuthoredLookupValid sourceValue) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.rangeExpression2).Contains (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.AddSubCached.native.range16Queries.get ⟨2, by decide⟩
  have member := authored.2 query (List.get_mem Airbender.Compiler.LookupSourceNative.AddSubCached.native.range16Queries ⟨2, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.AddSubCached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.AddSubCached.native.field2_0.source.value (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.originalProjection)] := member nonzero
  have present : Airbender.Compiler.LookupNative.AddSubCached.native.field2_0.source ∈ Airbender.Compiler.QueryFrameNative.AddSubCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.AddSubCached.native.fields ⟨11, by decide⟩
  have transported := Airbender.Compiler.QueryFrameNative.AddSubCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.AddSubCached.native.field2_0.source present
  have same := (Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.range_value2 physical data arithmetic).trans transported
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.AddSubCached.native.range16_clean_refinement _ valid _

theorem range_lookup3
    (sourceValue : Fin 48 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.AddSubCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.AddSubCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.AddSubCached.native.assigned (Airbender.Compiler.HelperValidityNative.AddSubCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.AddSubCached.AuthoredLookupValid sourceValue) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.rangeExpression3).Contains (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.AddSubCached.native.range16Queries.get ⟨3, by decide⟩
  have member := authored.2 query (List.get_mem Airbender.Compiler.LookupSourceNative.AddSubCached.native.range16Queries ⟨3, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.AddSubCached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.AddSubCached.native.field3_0.source.value (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.originalProjection)] := member nonzero
  have present : Airbender.Compiler.LookupNative.AddSubCached.native.field3_0.source ∈ Airbender.Compiler.QueryFrameNative.AddSubCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.AddSubCached.native.fields ⟨12, by decide⟩
  have transported := Airbender.Compiler.QueryFrameNative.AddSubCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.AddSubCached.native.field3_0.source present
  have same := (Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.range_value3 physical data arithmetic).trans transported
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.AddSubCached.native.range16_clean_refinement _ valid _

theorem range_lookup4
    (sourceValue : Fin 48 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.AddSubCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.AddSubCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.AddSubCached.native.assigned (Airbender.Compiler.HelperValidityNative.AddSubCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.AddSubCached.AuthoredLookupValid sourceValue) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.rangeExpression4).Contains (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.AddSubCached.native.range16Queries.get ⟨4, by decide⟩
  have member := authored.2 query (List.get_mem Airbender.Compiler.LookupSourceNative.AddSubCached.native.range16Queries ⟨4, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.AddSubCached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.AddSubCached.native.field4_0.source.value (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.originalProjection)] := member nonzero
  have present : Airbender.Compiler.LookupNative.AddSubCached.native.field4_0.source ∈ Airbender.Compiler.QueryFrameNative.AddSubCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.AddSubCached.native.fields ⟨13, by decide⟩
  have transported := Airbender.Compiler.QueryFrameNative.AddSubCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.AddSubCached.native.field4_0.source present
  have same := (Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.range_value4 physical data arithmetic).trans transported
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.AddSubCached.native.range16_clean_refinement _ valid _

theorem range_lookup5
    (sourceValue : Fin 48 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.AddSubCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.AddSubCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.AddSubCached.native.assigned (Airbender.Compiler.HelperValidityNative.AddSubCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.AddSubCached.AuthoredLookupValid sourceValue) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.rangeExpression5).Contains (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.AddSubCached.native.range16Queries.get ⟨5, by decide⟩
  have member := authored.2 query (List.get_mem Airbender.Compiler.LookupSourceNative.AddSubCached.native.range16Queries ⟨5, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.AddSubCached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.AddSubCached.native.field5_0.source.value (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.originalProjection)] := member nonzero
  have present : Airbender.Compiler.LookupNative.AddSubCached.native.field5_0.source ∈ Airbender.Compiler.QueryFrameNative.AddSubCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.AddSubCached.native.fields ⟨14, by decide⟩
  have transported := Airbender.Compiler.QueryFrameNative.AddSubCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.AddSubCached.native.field5_0.source present
  have same := (Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.range_value5 physical data arithmetic).trans transported
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.AddSubCached.native.range16_clean_refinement _ valid _

theorem retained_clock_from_source
    (sourceValue : Fin 48 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.AddSubCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.AddSubCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.AddSubCached.native.assigned (Airbender.Compiler.HelperValidityNative.AddSubCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address) = 0)
    (helpers : ∀ field ∈ Airbender.Compiler.HelperNative.AddSubCached.native.fields, (field.value (Airbender.Compiler.HelperNative.AddSubCached.native.sourceValues physical)).val < 524288)
    (authored : Airbender.Compiler.MaterializedWitnessNative.AddSubCached.AuthoredLookupValid sourceValue) :
    FlatOperation.ConstraintsHoldFlat (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment physical data) (Airbender.AddSub.clockConstraints (p := babyBearModulus)) := by
  apply Airbender.Compiler.CleanLinksNative.AddSubCached.retained_clock_constraints physical data arithmetic
  rw [clock_lookup_inventory]
  exact PredicateChecks.all (PredicateChecks.cons (range_lookup0 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (range_lookup1 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (range_lookup2 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (range_lookup3 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (range_lookup4 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (range_lookup5 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.timestampExpression0 (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.timestamp_bound0 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.timestampExpression1 (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.timestamp_bound1 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.timestampExpression2 (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.timestamp_bound2 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.timestampExpression3 (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.timestamp_bound3 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.timestampExpression4 (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.timestamp_bound4 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.timestampExpression5 (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.timestamp_bound5 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.timestampExpression6 (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.timestamp_bound6 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.timestampExpression7 (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.timestamp_bound7 physical data arithmetic helpers)) PredicateChecks.nil))))))))))))))

end Airbender.Compiler.CleanClosedNative.AddSubCached
