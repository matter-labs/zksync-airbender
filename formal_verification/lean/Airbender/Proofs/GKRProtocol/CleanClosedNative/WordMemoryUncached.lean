import Airbender.Proofs.GKRProtocol.CleanArgumentsNative.WordMemoryUncached
import Airbender.Proofs.GKRProtocol.CleanScalarNative.WordMemoryUncached
import Airbender.Proofs.GKRProtocol.CleanPrimitiveLookups
import Airbender.Proofs.GKRProtocol.CleanLinksNative.WordMemoryUncached
import Airbender.Proofs.GKRProtocol.MaterializedWitnessNative.WordMemoryUncached
import Airbender.Proofs.GKRProtocol.CleanGenericArgumentsNative.WordMemoryUncached
import Airbender.Proofs.GKRProtocol.CleanGenericSetup

namespace Airbender.Compiler.CleanClosedNative.WordMemoryUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

noncomputable def nativeSetup : Table Source.BaseField (fields 9) :=
  Airbender.Compiler.MaterializedNative.WordMemoryUncached.native.model.imported.data.table "Airbender.Native.WordMemory"

theorem generic_columns_inventory : Airbender.Compiler.TableNative.WordMemoryUncached.native.genericSetupColumns =
    (List.range 9).map SourceSetupColumn.generic := by decide +kernel

theorem clock_lookup_inventory :
    FlatOperation.lookups (Airbender.WordMemory.clockConstraints (p := babyBearModulus) nativeSetup) =
    (Airbender.Compiler.CleanArgumentsNative.WordMemoryUncached.native.rangeExpressions.map Verification.range16) ++
    (Airbender.Compiler.CleanGenericArgumentsNative.WordMemoryUncached.native.genericExpressions.map (fun entry => Lookup.mk nativeSetup.toRaw entry)) ++
    (Airbender.Compiler.CleanArgumentsNative.WordMemoryUncached.native.timestampExpressions.map Trace.timestampLookup) := by rfl

theorem range_lookup0
    (sourceValue : Fin 52 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.WordMemoryUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.WordMemoryUncached.native.assigned (Airbender.Compiler.HelperValidityNative.WordMemoryUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.WordMemoryUncached.AuthoredLookupValid sourceValue) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.WordMemoryUncached.native.rangeExpression0).Contains (Airbender.Compiler.CleanArithmeticNative.WordMemoryUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.range16Queries.get ⟨0, by decide⟩
  have member := authored.2 query (List.get_mem Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.range16Queries ⟨0, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.WordMemoryUncached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.WordMemoryUncached.native.field1_0.source.value (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.originalProjection)] := member nonzero
  have present : Airbender.Compiler.LookupNative.WordMemoryUncached.native.field1_0.source ∈ Airbender.Compiler.QueryFrameNative.WordMemoryUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.WordMemoryUncached.native.fields ⟨19, by decide⟩
  have transported := Airbender.Compiler.QueryFrameNative.WordMemoryUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.WordMemoryUncached.native.field1_0.source present
  have same := (Airbender.Compiler.CleanArgumentsNative.WordMemoryUncached.native.range_value0 physical data arithmetic).trans transported
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.WordMemoryUncached.native.range16_clean_refinement _ valid _

theorem range_lookup1
    (sourceValue : Fin 52 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.WordMemoryUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.WordMemoryUncached.native.assigned (Airbender.Compiler.HelperValidityNative.WordMemoryUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.WordMemoryUncached.AuthoredLookupValid sourceValue) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.WordMemoryUncached.native.rangeExpression1).Contains (Airbender.Compiler.CleanArithmeticNative.WordMemoryUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.range16Queries.get ⟨1, by decide⟩
  have member := authored.2 query (List.get_mem Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.range16Queries ⟨1, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.WordMemoryUncached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.WordMemoryUncached.native.field2_0.source.value (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.originalProjection)] := member nonzero
  have present : Airbender.Compiler.LookupNative.WordMemoryUncached.native.field2_0.source ∈ Airbender.Compiler.QueryFrameNative.WordMemoryUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.WordMemoryUncached.native.fields ⟨20, by decide⟩
  have transported := Airbender.Compiler.QueryFrameNative.WordMemoryUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.WordMemoryUncached.native.field2_0.source present
  have same := (Airbender.Compiler.CleanArgumentsNative.WordMemoryUncached.native.range_value1 physical data arithmetic).trans transported
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.WordMemoryUncached.native.range16_clean_refinement _ valid _

theorem range_lookup2
    (sourceValue : Fin 52 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.WordMemoryUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.WordMemoryUncached.native.assigned (Airbender.Compiler.HelperValidityNative.WordMemoryUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.WordMemoryUncached.AuthoredLookupValid sourceValue) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.WordMemoryUncached.native.rangeExpression2).Contains (Airbender.Compiler.CleanArithmeticNative.WordMemoryUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.range16Queries.get ⟨2, by decide⟩
  have member := authored.2 query (List.get_mem Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.range16Queries ⟨2, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.WordMemoryUncached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.WordMemoryUncached.native.field3_0.source.value (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.originalProjection)] := member nonzero
  have present : Airbender.Compiler.LookupNative.WordMemoryUncached.native.field3_0.source ∈ Airbender.Compiler.QueryFrameNative.WordMemoryUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.WordMemoryUncached.native.fields ⟨21, by decide⟩
  have transported := Airbender.Compiler.QueryFrameNative.WordMemoryUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.WordMemoryUncached.native.field3_0.source present
  have same := (Airbender.Compiler.CleanArgumentsNative.WordMemoryUncached.native.range_value2 physical data arithmetic).trans transported
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.WordMemoryUncached.native.range16_clean_refinement _ valid _

theorem generic_lookup0
    (sourceValue : Fin 52 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.WordMemoryUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.WordMemoryUncached.native.assigned (Airbender.Compiler.HelperValidityNative.WordMemoryUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.WordMemoryUncached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.WordMemoryUncached.native.genericExpressions0).Contains (Airbender.Compiler.CleanArithmeticNative.WordMemoryUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.genericQueries.get ⟨0, by decide⟩
  have member := authored.1 query (List.get_mem Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.genericQueries ⟨0, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.WordMemoryUncached.native.field0_0.source ∈ Airbender.Compiler.QueryFrameNative.WordMemoryUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.WordMemoryUncached.native.fields ⟨0, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.WordMemoryUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.WordMemoryUncached.native.field0_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.WordMemoryUncached.native.part0.generic_value0_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.WordMemoryUncached.native.field0_1.source ∈ Airbender.Compiler.QueryFrameNative.WordMemoryUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.WordMemoryUncached.native.fields ⟨1, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.WordMemoryUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.WordMemoryUncached.native.field0_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.WordMemoryUncached.native.part0.generic_value0_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.WordMemoryUncached.native.field0_2.source ∈ Airbender.Compiler.QueryFrameNative.WordMemoryUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.WordMemoryUncached.native.fields ⟨2, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.WordMemoryUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.WordMemoryUncached.native.field0_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.WordMemoryUncached.native.part0.generic_value0_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.WordMemoryUncached.native.field0_3.source ∈ Airbender.Compiler.QueryFrameNative.WordMemoryUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.WordMemoryUncached.native.fields ⟨3, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.WordMemoryUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.WordMemoryUncached.native.field0_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.WordMemoryUncached.native.part0.generic_value0_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.WordMemoryUncached.native.field0_4.source ∈ Airbender.Compiler.QueryFrameNative.WordMemoryUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.WordMemoryUncached.native.fields ⟨4, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.WordMemoryUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.WordMemoryUncached.native.field0_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.WordMemoryUncached.native.part0.generic_value0_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.WordMemoryUncached.native.field0_5.source ∈ Airbender.Compiler.QueryFrameNative.WordMemoryUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.WordMemoryUncached.native.fields ⟨5, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.WordMemoryUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.WordMemoryUncached.native.field0_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.WordMemoryUncached.native.part0.generic_value0_5 physical data arithmetic).trans transported5
  have present6 : Airbender.Compiler.LookupNative.WordMemoryUncached.native.field0_6.source ∈ Airbender.Compiler.QueryFrameNative.WordMemoryUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.WordMemoryUncached.native.fields ⟨6, by decide⟩
  have transported6 := Airbender.Compiler.QueryFrameNative.WordMemoryUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.WordMemoryUncached.native.field0_6.source present6
  have same6 := (Airbender.Compiler.CleanGenericArgumentsNative.WordMemoryUncached.native.part0.generic_value0_6 physical data arithmetic).trans transported6
  have present7 : Airbender.Compiler.LookupNative.WordMemoryUncached.native.field0_7.source ∈ Airbender.Compiler.QueryFrameNative.WordMemoryUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.WordMemoryUncached.native.fields ⟨7, by decide⟩
  have transported7 := Airbender.Compiler.QueryFrameNative.WordMemoryUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.WordMemoryUncached.native.field0_7.source present7
  have same7 := (Airbender.Compiler.CleanGenericArgumentsNative.WordMemoryUncached.native.part0.generic_value0_7 physical data arithmetic).trans transported7
  have present8 : Airbender.Compiler.LookupNative.WordMemoryUncached.native.field0_8.source ∈ Airbender.Compiler.QueryFrameNative.WordMemoryUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.WordMemoryUncached.native.fields ⟨8, by decide⟩
  have transported8 := Airbender.Compiler.QueryFrameNative.WordMemoryUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.WordMemoryUncached.native.field0_8.source present8
  have same8 := (Airbender.Compiler.CleanGenericArgumentsNative.WordMemoryUncached.native.part0.generic_value0_8 physical data arithmetic).trans transported8
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.WordMemoryUncached.native.model.generic_clean_contains Airbender.Compiler.TableNative.WordMemoryUncached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.WordMemory" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.WordMemoryUncached.native.genericExpressions0, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.WordMemoryUncached.native.model.Contains Airbender.Compiler.TableNative.WordMemoryUncached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.WordMemoryUncached.native.part0.genericExpression0_0.eval (Airbender.Compiler.CleanArithmeticNative.WordMemoryUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.WordMemoryUncached.native.part0.genericExpression0_1.eval (Airbender.Compiler.CleanArithmeticNative.WordMemoryUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.WordMemoryUncached.native.part0.genericExpression0_2.eval (Airbender.Compiler.CleanArithmeticNative.WordMemoryUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.WordMemoryUncached.native.part0.genericExpression0_3.eval (Airbender.Compiler.CleanArithmeticNative.WordMemoryUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.WordMemoryUncached.native.part0.genericExpression0_4.eval (Airbender.Compiler.CleanArithmeticNative.WordMemoryUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.WordMemoryUncached.native.part0.genericExpression0_5.eval (Airbender.Compiler.CleanArithmeticNative.WordMemoryUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.WordMemoryUncached.native.part0.genericExpression0_6.eval (Airbender.Compiler.CleanArithmeticNative.WordMemoryUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.WordMemoryUncached.native.part0.genericExpression0_7.eval (Airbender.Compiler.CleanArithmeticNative.WordMemoryUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.WordMemoryUncached.native.part0.genericExpression0_8.eval (Airbender.Compiler.CleanArithmeticNative.WordMemoryUncached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5, same6, same7, same8]
  exact valid

theorem retained_clock_from_source
    (sourceValue : Fin 52 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.WordMemoryUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.WordMemoryUncached.native.assigned (Airbender.Compiler.HelperValidityNative.WordMemoryUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.bank.address) = 0)
    (helpers : ∀ field ∈ Airbender.Compiler.HelperNative.WordMemoryUncached.native.fields, (field.value (Airbender.Compiler.HelperNative.WordMemoryUncached.native.sourceValues physical)).val < 524288)
    (authored : Airbender.Compiler.MaterializedWitnessNative.WordMemoryUncached.AuthoredLookupValid sourceValue) :
    FlatOperation.ConstraintsHoldFlat (Airbender.Compiler.CleanArithmeticNative.WordMemoryUncached.native.environment physical data) (Airbender.WordMemory.clockConstraints (p := babyBearModulus) nativeSetup) := by
  apply Airbender.Compiler.CleanLinksNative.WordMemoryUncached.retained_clock_constraints nativeSetup physical data arithmetic
  rw [clock_lookup_inventory]
  exact PredicateChecks.all (PredicateChecks.cons (range_lookup0 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (range_lookup1 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (range_lookup2 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (generic_lookup0 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.WordMemoryUncached.native.timestampExpression0 (Airbender.Compiler.CleanArithmeticNative.WordMemoryUncached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.WordMemoryUncached.native.timestamp_bound0 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.WordMemoryUncached.native.timestampExpression1 (Airbender.Compiler.CleanArithmeticNative.WordMemoryUncached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.WordMemoryUncached.native.timestamp_bound1 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.WordMemoryUncached.native.timestampExpression2 (Airbender.Compiler.CleanArithmeticNative.WordMemoryUncached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.WordMemoryUncached.native.timestamp_bound2 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.WordMemoryUncached.native.timestampExpression3 (Airbender.Compiler.CleanArithmeticNative.WordMemoryUncached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.WordMemoryUncached.native.timestamp_bound3 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.WordMemoryUncached.native.timestampExpression4 (Airbender.Compiler.CleanArithmeticNative.WordMemoryUncached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.WordMemoryUncached.native.timestamp_bound4 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.WordMemoryUncached.native.timestampExpression5 (Airbender.Compiler.CleanArithmeticNative.WordMemoryUncached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.WordMemoryUncached.native.timestamp_bound5 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.WordMemoryUncached.native.timestampExpression6 (Airbender.Compiler.CleanArithmeticNative.WordMemoryUncached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.WordMemoryUncached.native.timestamp_bound6 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.WordMemoryUncached.native.timestampExpression7 (Airbender.Compiler.CleanArithmeticNative.WordMemoryUncached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.WordMemoryUncached.native.timestamp_bound7 physical data arithmetic helpers)) PredicateChecks.nil))))))))))))

end Airbender.Compiler.CleanClosedNative.WordMemoryUncached
