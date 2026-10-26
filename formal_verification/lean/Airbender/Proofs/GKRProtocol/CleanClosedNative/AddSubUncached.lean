import Airbender.Proofs.GKRProtocol.CleanArgumentsNative.AddSubUncached
import Airbender.Proofs.GKRProtocol.CleanScalarNative.AddSubUncached
import Airbender.Proofs.GKRProtocol.CleanPrimitiveLookups
import Airbender.Proofs.GKRProtocol.CleanLinksNative.AddSubUncached
import Airbender.Proofs.GKRProtocol.MaterializedWitnessNative.AddSubUncached

namespace Airbender.Compiler.CleanClosedNative.AddSubUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

theorem clock_lookup_inventory :
    FlatOperation.lookups (Airbender.AddSub.clockConstraints (p := babyBearModulus)) =
    (Airbender.Compiler.CleanArgumentsNative.AddSubUncached.native.rangeExpressions.map Verification.range16) ++
    (Airbender.Compiler.CleanArgumentsNative.AddSubUncached.native.timestampExpressions.map Trace.timestampLookup) := by rfl

theorem range_lookup0
    (sourceValue : Fin 48 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.AddSubUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.AddSubUncached.native.assigned (Airbender.Compiler.HelperValidityNative.AddSubUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.AddSubUncached.AuthoredLookupValid sourceValue) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.AddSubUncached.native.rangeExpression0).Contains (Airbender.Compiler.CleanArithmeticNative.AddSubUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.AddSubUncached.native.range16Queries.get ⟨0, by decide⟩
  have member := authored.2 query (List.get_mem Airbender.Compiler.LookupSourceNative.AddSubUncached.native.range16Queries ⟨0, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.AddSubUncached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.AddSubUncached.native.field0_0.source.value (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.originalProjection)] := member nonzero
  have present : Airbender.Compiler.LookupNative.AddSubUncached.native.field0_0.source ∈ Airbender.Compiler.QueryFrameNative.AddSubUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.AddSubUncached.native.fields ⟨9, by decide⟩
  have transported := Airbender.Compiler.QueryFrameNative.AddSubUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.AddSubUncached.native.field0_0.source present
  have same := (Airbender.Compiler.CleanArgumentsNative.AddSubUncached.native.range_value0 physical data arithmetic).trans transported
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.AddSubUncached.native.range16_clean_refinement _ valid _

theorem range_lookup1
    (sourceValue : Fin 48 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.AddSubUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.AddSubUncached.native.assigned (Airbender.Compiler.HelperValidityNative.AddSubUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.AddSubUncached.AuthoredLookupValid sourceValue) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.AddSubUncached.native.rangeExpression1).Contains (Airbender.Compiler.CleanArithmeticNative.AddSubUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.AddSubUncached.native.range16Queries.get ⟨1, by decide⟩
  have member := authored.2 query (List.get_mem Airbender.Compiler.LookupSourceNative.AddSubUncached.native.range16Queries ⟨1, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.AddSubUncached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.AddSubUncached.native.field1_0.source.value (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.originalProjection)] := member nonzero
  have present : Airbender.Compiler.LookupNative.AddSubUncached.native.field1_0.source ∈ Airbender.Compiler.QueryFrameNative.AddSubUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.AddSubUncached.native.fields ⟨10, by decide⟩
  have transported := Airbender.Compiler.QueryFrameNative.AddSubUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.AddSubUncached.native.field1_0.source present
  have same := (Airbender.Compiler.CleanArgumentsNative.AddSubUncached.native.range_value1 physical data arithmetic).trans transported
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.AddSubUncached.native.range16_clean_refinement _ valid _

theorem range_lookup2
    (sourceValue : Fin 48 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.AddSubUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.AddSubUncached.native.assigned (Airbender.Compiler.HelperValidityNative.AddSubUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.AddSubUncached.AuthoredLookupValid sourceValue) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.AddSubUncached.native.rangeExpression2).Contains (Airbender.Compiler.CleanArithmeticNative.AddSubUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.AddSubUncached.native.range16Queries.get ⟨2, by decide⟩
  have member := authored.2 query (List.get_mem Airbender.Compiler.LookupSourceNative.AddSubUncached.native.range16Queries ⟨2, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.AddSubUncached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.AddSubUncached.native.field2_0.source.value (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.originalProjection)] := member nonzero
  have present : Airbender.Compiler.LookupNative.AddSubUncached.native.field2_0.source ∈ Airbender.Compiler.QueryFrameNative.AddSubUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.AddSubUncached.native.fields ⟨11, by decide⟩
  have transported := Airbender.Compiler.QueryFrameNative.AddSubUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.AddSubUncached.native.field2_0.source present
  have same := (Airbender.Compiler.CleanArgumentsNative.AddSubUncached.native.range_value2 physical data arithmetic).trans transported
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.AddSubUncached.native.range16_clean_refinement _ valid _

theorem range_lookup3
    (sourceValue : Fin 48 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.AddSubUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.AddSubUncached.native.assigned (Airbender.Compiler.HelperValidityNative.AddSubUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.AddSubUncached.AuthoredLookupValid sourceValue) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.AddSubUncached.native.rangeExpression3).Contains (Airbender.Compiler.CleanArithmeticNative.AddSubUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.AddSubUncached.native.range16Queries.get ⟨3, by decide⟩
  have member := authored.2 query (List.get_mem Airbender.Compiler.LookupSourceNative.AddSubUncached.native.range16Queries ⟨3, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.AddSubUncached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.AddSubUncached.native.field3_0.source.value (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.originalProjection)] := member nonzero
  have present : Airbender.Compiler.LookupNative.AddSubUncached.native.field3_0.source ∈ Airbender.Compiler.QueryFrameNative.AddSubUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.AddSubUncached.native.fields ⟨12, by decide⟩
  have transported := Airbender.Compiler.QueryFrameNative.AddSubUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.AddSubUncached.native.field3_0.source present
  have same := (Airbender.Compiler.CleanArgumentsNative.AddSubUncached.native.range_value3 physical data arithmetic).trans transported
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.AddSubUncached.native.range16_clean_refinement _ valid _

theorem range_lookup4
    (sourceValue : Fin 48 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.AddSubUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.AddSubUncached.native.assigned (Airbender.Compiler.HelperValidityNative.AddSubUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.AddSubUncached.AuthoredLookupValid sourceValue) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.AddSubUncached.native.rangeExpression4).Contains (Airbender.Compiler.CleanArithmeticNative.AddSubUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.AddSubUncached.native.range16Queries.get ⟨4, by decide⟩
  have member := authored.2 query (List.get_mem Airbender.Compiler.LookupSourceNative.AddSubUncached.native.range16Queries ⟨4, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.AddSubUncached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.AddSubUncached.native.field4_0.source.value (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.originalProjection)] := member nonzero
  have present : Airbender.Compiler.LookupNative.AddSubUncached.native.field4_0.source ∈ Airbender.Compiler.QueryFrameNative.AddSubUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.AddSubUncached.native.fields ⟨13, by decide⟩
  have transported := Airbender.Compiler.QueryFrameNative.AddSubUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.AddSubUncached.native.field4_0.source present
  have same := (Airbender.Compiler.CleanArgumentsNative.AddSubUncached.native.range_value4 physical data arithmetic).trans transported
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.AddSubUncached.native.range16_clean_refinement _ valid _

theorem range_lookup5
    (sourceValue : Fin 48 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.AddSubUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.AddSubUncached.native.assigned (Airbender.Compiler.HelperValidityNative.AddSubUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.AddSubUncached.AuthoredLookupValid sourceValue) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.AddSubUncached.native.rangeExpression5).Contains (Airbender.Compiler.CleanArithmeticNative.AddSubUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.AddSubUncached.native.range16Queries.get ⟨5, by decide⟩
  have member := authored.2 query (List.get_mem Airbender.Compiler.LookupSourceNative.AddSubUncached.native.range16Queries ⟨5, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.AddSubUncached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.AddSubUncached.native.field5_0.source.value (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.originalProjection)] := member nonzero
  have present : Airbender.Compiler.LookupNative.AddSubUncached.native.field5_0.source ∈ Airbender.Compiler.QueryFrameNative.AddSubUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.AddSubUncached.native.fields ⟨14, by decide⟩
  have transported := Airbender.Compiler.QueryFrameNative.AddSubUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.AddSubUncached.native.field5_0.source present
  have same := (Airbender.Compiler.CleanArgumentsNative.AddSubUncached.native.range_value5 physical data arithmetic).trans transported
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.AddSubUncached.native.range16_clean_refinement _ valid _

theorem retained_clock_from_source
    (sourceValue : Fin 48 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.AddSubUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.AddSubUncached.native.assigned (Airbender.Compiler.HelperValidityNative.AddSubUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.bank.address) = 0)
    (helpers : ∀ field ∈ Airbender.Compiler.HelperNative.AddSubUncached.native.fields, (field.value (Airbender.Compiler.HelperNative.AddSubUncached.native.sourceValues physical)).val < 524288)
    (authored : Airbender.Compiler.MaterializedWitnessNative.AddSubUncached.AuthoredLookupValid sourceValue) :
    FlatOperation.ConstraintsHoldFlat (Airbender.Compiler.CleanArithmeticNative.AddSubUncached.native.environment physical data) (Airbender.AddSub.clockConstraints (p := babyBearModulus)) := by
  apply Airbender.Compiler.CleanLinksNative.AddSubUncached.retained_clock_constraints physical data arithmetic
  rw [clock_lookup_inventory]
  exact PredicateChecks.all (PredicateChecks.cons (range_lookup0 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (range_lookup1 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (range_lookup2 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (range_lookup3 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (range_lookup4 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (range_lookup5 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.AddSubUncached.native.timestampExpression0 (Airbender.Compiler.CleanArithmeticNative.AddSubUncached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.AddSubUncached.native.timestamp_bound0 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.AddSubUncached.native.timestampExpression1 (Airbender.Compiler.CleanArithmeticNative.AddSubUncached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.AddSubUncached.native.timestamp_bound1 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.AddSubUncached.native.timestampExpression2 (Airbender.Compiler.CleanArithmeticNative.AddSubUncached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.AddSubUncached.native.timestamp_bound2 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.AddSubUncached.native.timestampExpression3 (Airbender.Compiler.CleanArithmeticNative.AddSubUncached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.AddSubUncached.native.timestamp_bound3 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.AddSubUncached.native.timestampExpression4 (Airbender.Compiler.CleanArithmeticNative.AddSubUncached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.AddSubUncached.native.timestamp_bound4 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.AddSubUncached.native.timestampExpression5 (Airbender.Compiler.CleanArithmeticNative.AddSubUncached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.AddSubUncached.native.timestamp_bound5 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.AddSubUncached.native.timestampExpression6 (Airbender.Compiler.CleanArithmeticNative.AddSubUncached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.AddSubUncached.native.timestamp_bound6 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.AddSubUncached.native.timestampExpression7 (Airbender.Compiler.CleanArithmeticNative.AddSubUncached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.AddSubUncached.native.timestamp_bound7 physical data arithmetic helpers)) PredicateChecks.nil))))))))))))))

end Airbender.Compiler.CleanClosedNative.AddSubUncached
