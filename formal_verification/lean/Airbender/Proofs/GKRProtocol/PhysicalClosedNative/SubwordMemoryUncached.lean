import Airbender.Import.Compiler.LogicalRows.SubwordMemoryUncached
import Airbender.Proofs.GKRProtocol.CleanArgumentsNative.SubwordMemoryUncached
import Airbender.Proofs.GKRProtocol.CleanScalarNative.SubwordMemoryUncached
import Airbender.Proofs.GKRProtocol.CleanPrimitiveLookups
import Airbender.Proofs.GKRProtocol.CleanLinksNative.SubwordMemoryUncached
import Airbender.Proofs.GKRProtocol.MaterializedWitnessNative.SubwordMemoryUncached
import Airbender.Proofs.GKRProtocol.CleanGenericArgumentsNative.SubwordMemoryUncached
import Airbender.Proofs.GKRProtocol.CleanGenericSetup

namespace Airbender.Compiler.PhysicalClosedNative.SubwordMemoryUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

noncomputable def nativeSetup : Table Source.BaseField (fields 9) :=
  Airbender.Compiler.MaterializedNative.SubwordMemoryUncached.native.model.imported.data.table "Airbender.Native.SubwordMemory"

theorem generic_columns_inventory : Airbender.Compiler.TableNative.SubwordMemoryUncached.native.genericSetupColumns =
    (List.range 9).map SourceSetupColumn.generic := by decide +kernel

theorem clock_lookup_inventory :
    FlatOperation.lookups (Airbender.SubwordMemory.clockConstraints (p := babyBearModulus) nativeSetup) =
    (Airbender.Compiler.CleanArgumentsNative.SubwordMemoryUncached.native.rangeExpressions.map Verification.range16) ++
    (Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryUncached.native.genericExpressions.map (fun entry => Lookup.mk nativeSetup.toRaw entry)) ++
    (Airbender.Compiler.CleanArgumentsNative.SubwordMemoryUncached.native.timestampExpressions.map Trace.timestampLookup) := by rfl

theorem range_lookup0
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.PooledRowNative.SubwordMemoryUncached.PhysicalAuthoredLookupValid physical) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.SubwordMemoryUncached.native.rangeExpression0).Contains (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.range16Queries.get ⟨0, by decide⟩
  have member := authored.2 query (List.get_mem Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.range16Queries ⟨0, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.SubwordMemoryUncached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.field2_0.source.value ((physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement)] := member nonzero
  have same := (Airbender.Compiler.CleanArgumentsNative.SubwordMemoryUncached.native.range_value0 physical data arithmetic)
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.SubwordMemoryUncached.native.range16_clean_refinement _ valid _

theorem range_lookup1
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.PooledRowNative.SubwordMemoryUncached.PhysicalAuthoredLookupValid physical) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.SubwordMemoryUncached.native.rangeExpression1).Contains (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.range16Queries.get ⟨1, by decide⟩
  have member := authored.2 query (List.get_mem Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.range16Queries ⟨1, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.SubwordMemoryUncached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.field3_0.source.value ((physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement)] := member nonzero
  have same := (Airbender.Compiler.CleanArgumentsNative.SubwordMemoryUncached.native.range_value1 physical data arithmetic)
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.SubwordMemoryUncached.native.range16_clean_refinement _ valid _

theorem range_lookup2
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.PooledRowNative.SubwordMemoryUncached.PhysicalAuthoredLookupValid physical) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.SubwordMemoryUncached.native.rangeExpression2).Contains (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.range16Queries.get ⟨2, by decide⟩
  have member := authored.2 query (List.get_mem Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.range16Queries ⟨2, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.SubwordMemoryUncached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.field4_0.source.value ((physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement)] := member nonzero
  have same := (Airbender.Compiler.CleanArgumentsNative.SubwordMemoryUncached.native.range_value2 physical data arithmetic)
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.SubwordMemoryUncached.native.range16_clean_refinement _ valid _

theorem range_lookup3
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.PooledRowNative.SubwordMemoryUncached.PhysicalAuthoredLookupValid physical) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.SubwordMemoryUncached.native.rangeExpression3).Contains (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.range16Queries.get ⟨3, by decide⟩
  have member := authored.2 query (List.get_mem Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.range16Queries ⟨3, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.SubwordMemoryUncached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.field5_0.source.value ((physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement)] := member nonzero
  have same := (Airbender.Compiler.CleanArgumentsNative.SubwordMemoryUncached.native.range_value3 physical data arithmetic)
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.SubwordMemoryUncached.native.range16_clean_refinement _ valid _

theorem range_lookup4
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.PooledRowNative.SubwordMemoryUncached.PhysicalAuthoredLookupValid physical) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.SubwordMemoryUncached.native.rangeExpression4).Contains (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.range16Queries.get ⟨4, by decide⟩
  have member := authored.2 query (List.get_mem Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.range16Queries ⟨4, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.SubwordMemoryUncached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.field6_0.source.value ((physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement)] := member nonzero
  have same := (Airbender.Compiler.CleanArgumentsNative.SubwordMemoryUncached.native.range_value4 physical data arithmetic)
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.SubwordMemoryUncached.native.range16_clean_refinement _ valid _

theorem generic_lookup0
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.PooledRowNative.SubwordMemoryUncached.PhysicalAuthoredLookupValid physical) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryUncached.native.genericExpressions0).Contains (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.genericQueries.get ⟨0, by decide⟩
  have member := authored.1 query (List.get_mem Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.genericQueries ⟨0, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryUncached.native.part0.generic_value0_0 physical data arithmetic)
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryUncached.native.part0.generic_value0_1 physical data arithmetic)
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryUncached.native.part0.generic_value0_2 physical data arithmetic)
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryUncached.native.part0.generic_value0_3 physical data arithmetic)
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryUncached.native.part0.generic_value0_4 physical data arithmetic)
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryUncached.native.part0.generic_value0_5 physical data arithmetic)
  have same6 := (Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryUncached.native.part0.generic_value0_6 physical data arithmetic)
  have same7 := (Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryUncached.native.part0.generic_value0_7 physical data arithmetic)
  have same8 := (Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryUncached.native.part0.generic_value0_8 physical data arithmetic)
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.SubwordMemoryUncached.native.model.generic_clean_contains Airbender.Compiler.TableNative.SubwordMemoryUncached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.SubwordMemory" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryUncached.native.genericExpressions0, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.SubwordMemoryUncached.native.model.Contains Airbender.Compiler.TableNative.SubwordMemoryUncached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryUncached.native.part0.genericExpression0_0.eval (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryUncached.native.part0.genericExpression0_1.eval (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryUncached.native.part0.genericExpression0_2.eval (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryUncached.native.part0.genericExpression0_3.eval (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryUncached.native.part0.genericExpression0_4.eval (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryUncached.native.part0.genericExpression0_5.eval (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryUncached.native.part0.genericExpression0_6.eval (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryUncached.native.part0.genericExpression0_7.eval (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryUncached.native.part0.genericExpression0_8.eval (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5, same6, same7, same8]
  exact valid

theorem generic_lookup1
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.PooledRowNative.SubwordMemoryUncached.PhysicalAuthoredLookupValid physical) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryUncached.native.genericExpressions1).Contains (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.genericQueries.get ⟨1, by decide⟩
  have member := authored.1 query (List.get_mem Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.genericQueries ⟨1, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryUncached.native.part0.generic_value1_0 physical data arithmetic)
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryUncached.native.part0.generic_value1_1 physical data arithmetic)
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryUncached.native.part0.generic_value1_2 physical data arithmetic)
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryUncached.native.part0.generic_value1_3 physical data arithmetic)
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryUncached.native.part0.generic_value1_4 physical data arithmetic)
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryUncached.native.part0.generic_value1_5 physical data arithmetic)
  have same6 := (Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryUncached.native.part0.generic_value1_6 physical data arithmetic)
  have same7 := (Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryUncached.native.part0.generic_value1_7 physical data arithmetic)
  have same8 := (Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryUncached.native.part0.generic_value1_8 physical data arithmetic)
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.SubwordMemoryUncached.native.model.generic_clean_contains Airbender.Compiler.TableNative.SubwordMemoryUncached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.SubwordMemory" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryUncached.native.genericExpressions1, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.SubwordMemoryUncached.native.model.Contains Airbender.Compiler.TableNative.SubwordMemoryUncached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryUncached.native.part0.genericExpression1_0.eval (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryUncached.native.part0.genericExpression1_1.eval (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryUncached.native.part0.genericExpression1_2.eval (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryUncached.native.part0.genericExpression1_3.eval (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryUncached.native.part0.genericExpression1_4.eval (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryUncached.native.part0.genericExpression1_5.eval (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryUncached.native.part0.genericExpression1_6.eval (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryUncached.native.part0.genericExpression1_7.eval (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryUncached.native.part0.genericExpression1_8.eval (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5, same6, same7, same8]
  exact valid

theorem retained_clock_from_physical
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.bank.address) = 0)
    (helpers : ∀ field ∈ Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.fields, (field.value (Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.sourceValues physical)).val < 524288)
    (authored : Airbender.Compiler.PooledRowNative.SubwordMemoryUncached.PhysicalAuthoredLookupValid physical) :
    FlatOperation.ConstraintsHoldFlat (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment physical data) (Airbender.SubwordMemory.clockConstraints (p := babyBearModulus) nativeSetup) := by
  apply Airbender.Compiler.CleanLinksNative.SubwordMemoryUncached.retained_clock_constraints nativeSetup physical data arithmetic
  rw [clock_lookup_inventory]
  exact PredicateChecks.all (PredicateChecks.cons (range_lookup0 physical data arithmetic authored) (PredicateChecks.cons (range_lookup1 physical data arithmetic authored) (PredicateChecks.cons (range_lookup2 physical data arithmetic authored) (PredicateChecks.cons (range_lookup3 physical data arithmetic authored) (PredicateChecks.cons (range_lookup4 physical data arithmetic authored) (PredicateChecks.cons (generic_lookup0 physical data arithmetic authored) (PredicateChecks.cons (generic_lookup1 physical data arithmetic authored) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.SubwordMemoryUncached.native.timestampExpression0 (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.SubwordMemoryUncached.native.timestamp_bound0 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.SubwordMemoryUncached.native.timestampExpression1 (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.SubwordMemoryUncached.native.timestamp_bound1 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.SubwordMemoryUncached.native.timestampExpression2 (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.SubwordMemoryUncached.native.timestamp_bound2 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.SubwordMemoryUncached.native.timestampExpression3 (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.SubwordMemoryUncached.native.timestamp_bound3 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.SubwordMemoryUncached.native.timestampExpression4 (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.SubwordMemoryUncached.native.timestamp_bound4 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.SubwordMemoryUncached.native.timestampExpression5 (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.SubwordMemoryUncached.native.timestamp_bound5 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.SubwordMemoryUncached.native.timestampExpression6 (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.SubwordMemoryUncached.native.timestamp_bound6 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.SubwordMemoryUncached.native.timestampExpression7 (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.SubwordMemoryUncached.native.timestamp_bound7 physical data arithmetic helpers)) PredicateChecks.nil)))))))))))))))

end Airbender.Compiler.PhysicalClosedNative.SubwordMemoryUncached
