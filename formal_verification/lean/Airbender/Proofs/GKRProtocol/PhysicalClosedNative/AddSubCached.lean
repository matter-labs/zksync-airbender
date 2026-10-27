import Airbender.Import.Compiler.LogicalRows.AddSubCached
import Airbender.Proofs.GKRProtocol.CleanArgumentsNative.AddSubCached
import Airbender.Proofs.GKRProtocol.CleanScalarNative.AddSubCached
import Airbender.Proofs.GKRProtocol.CleanPrimitiveLookups
import Airbender.Proofs.GKRProtocol.CleanLinksNative.AddSubCached
import Airbender.Proofs.GKRProtocol.MaterializedWitnessNative.AddSubCached

namespace Airbender.Compiler.PhysicalClosedNative.AddSubCached
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
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.PooledRowNative.AddSubCached.PhysicalAuthoredLookupValid physical) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.rangeExpression0).Contains (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.AddSubCached.native.range16Queries.get ⟨0, by decide⟩
  have member := authored.2 query (List.get_mem Airbender.Compiler.LookupSourceNative.AddSubCached.native.range16Queries ⟨0, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((physical ∘ Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.AddSubCached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.AddSubCached.native.field0_0.source.value ((physical ∘ Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement)] := member nonzero
  have same := (Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.range_value0 physical data arithmetic)
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.AddSubCached.native.range16_clean_refinement _ valid _

theorem range_lookup1
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.PooledRowNative.AddSubCached.PhysicalAuthoredLookupValid physical) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.rangeExpression1).Contains (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.AddSubCached.native.range16Queries.get ⟨1, by decide⟩
  have member := authored.2 query (List.get_mem Airbender.Compiler.LookupSourceNative.AddSubCached.native.range16Queries ⟨1, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((physical ∘ Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.AddSubCached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.AddSubCached.native.field1_0.source.value ((physical ∘ Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement)] := member nonzero
  have same := (Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.range_value1 physical data arithmetic)
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.AddSubCached.native.range16_clean_refinement _ valid _

theorem range_lookup2
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.PooledRowNative.AddSubCached.PhysicalAuthoredLookupValid physical) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.rangeExpression2).Contains (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.AddSubCached.native.range16Queries.get ⟨2, by decide⟩
  have member := authored.2 query (List.get_mem Airbender.Compiler.LookupSourceNative.AddSubCached.native.range16Queries ⟨2, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((physical ∘ Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.AddSubCached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.AddSubCached.native.field2_0.source.value ((physical ∘ Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement)] := member nonzero
  have same := (Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.range_value2 physical data arithmetic)
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.AddSubCached.native.range16_clean_refinement _ valid _

theorem range_lookup3
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.PooledRowNative.AddSubCached.PhysicalAuthoredLookupValid physical) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.rangeExpression3).Contains (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.AddSubCached.native.range16Queries.get ⟨3, by decide⟩
  have member := authored.2 query (List.get_mem Airbender.Compiler.LookupSourceNative.AddSubCached.native.range16Queries ⟨3, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((physical ∘ Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.AddSubCached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.AddSubCached.native.field3_0.source.value ((physical ∘ Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement)] := member nonzero
  have same := (Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.range_value3 physical data arithmetic)
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.AddSubCached.native.range16_clean_refinement _ valid _

theorem range_lookup4
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.PooledRowNative.AddSubCached.PhysicalAuthoredLookupValid physical) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.rangeExpression4).Contains (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.AddSubCached.native.range16Queries.get ⟨4, by decide⟩
  have member := authored.2 query (List.get_mem Airbender.Compiler.LookupSourceNative.AddSubCached.native.range16Queries ⟨4, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((physical ∘ Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.AddSubCached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.AddSubCached.native.field4_0.source.value ((physical ∘ Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement)] := member nonzero
  have same := (Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.range_value4 physical data arithmetic)
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.AddSubCached.native.range16_clean_refinement _ valid _

theorem range_lookup5
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.PooledRowNative.AddSubCached.PhysicalAuthoredLookupValid physical) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.rangeExpression5).Contains (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.AddSubCached.native.range16Queries.get ⟨5, by decide⟩
  have member := authored.2 query (List.get_mem Airbender.Compiler.LookupSourceNative.AddSubCached.native.range16Queries ⟨5, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((physical ∘ Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.AddSubCached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.AddSubCached.native.field5_0.source.value ((physical ∘ Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement)] := member nonzero
  have same := (Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.range_value5 physical data arithmetic)
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.AddSubCached.native.range16_clean_refinement _ valid _

theorem retained_clock_from_physical
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address) = 0)
    (helpers : ∀ field ∈ Airbender.Compiler.HelperNative.AddSubCached.native.fields, (field.value (Airbender.Compiler.HelperNative.AddSubCached.native.sourceValues physical)).val < 524288)
    (authored : Airbender.Compiler.PooledRowNative.AddSubCached.PhysicalAuthoredLookupValid physical) :
    FlatOperation.ConstraintsHoldFlat (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment physical data) (Airbender.AddSub.clockConstraints (p := babyBearModulus)) := by
  apply Airbender.Compiler.CleanLinksNative.AddSubCached.retained_clock_constraints physical data arithmetic
  rw [clock_lookup_inventory]
  exact PredicateChecks.all (PredicateChecks.cons (range_lookup0 physical data arithmetic authored) (PredicateChecks.cons (range_lookup1 physical data arithmetic authored) (PredicateChecks.cons (range_lookup2 physical data arithmetic authored) (PredicateChecks.cons (range_lookup3 physical data arithmetic authored) (PredicateChecks.cons (range_lookup4 physical data arithmetic authored) (PredicateChecks.cons (range_lookup5 physical data arithmetic authored) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.timestampExpression0 (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.timestamp_bound0 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.timestampExpression1 (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.timestamp_bound1 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.timestampExpression2 (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.timestamp_bound2 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.timestampExpression3 (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.timestamp_bound3 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.timestampExpression4 (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.timestamp_bound4 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.timestampExpression5 (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.timestamp_bound5 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.timestampExpression6 (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.timestamp_bound6 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.timestampExpression7 (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.timestamp_bound7 physical data arithmetic helpers)) PredicateChecks.nil))))))))))))))

end Airbender.Compiler.PhysicalClosedNative.AddSubCached
