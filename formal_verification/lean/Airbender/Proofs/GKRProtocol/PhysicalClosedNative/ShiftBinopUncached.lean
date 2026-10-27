import Airbender.Import.Compiler.LogicalRows.ShiftBinopUncached
import Airbender.Proofs.GKRProtocol.CleanArgumentsNative.ShiftBinopUncached
import Airbender.Proofs.GKRProtocol.CleanScalarNative.ShiftBinopUncached
import Airbender.Proofs.GKRProtocol.CleanPrimitiveLookups
import Airbender.Proofs.GKRProtocol.CleanLinksNative.ShiftBinopUncached
import Airbender.Proofs.GKRProtocol.MaterializedWitnessNative.ShiftBinopUncached
import Airbender.Proofs.GKRProtocol.CleanGenericArgumentsNative.ShiftBinopUncached
import Airbender.Proofs.GKRProtocol.ShiftSetupNative

namespace Airbender.Compiler.PhysicalClosedNative.ShiftBinopUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

noncomputable def nativeSetup : Table Source.BaseField (fields 10) :=
  Verification.shiftBinopTable (p := babyBearModulus)

theorem generic_columns_inventory : Airbender.Compiler.TableNative.ShiftBinopUncached.native.genericSetupColumns =
    (List.range 10).map SourceSetupColumn.generic := by decide +kernel

theorem clock_lookup_inventory :
    FlatOperation.lookups (Airbender.ShiftBinop.clockConstraints (p := babyBearModulus)) =
    (Airbender.Compiler.CleanArgumentsNative.ShiftBinopUncached.native.rangeExpressions.map Verification.range16) ++
    (Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.genericExpressions.map (fun entry => Lookup.mk nativeSetup.toRaw entry)) ++
    (Airbender.Compiler.CleanArgumentsNative.ShiftBinopUncached.native.timestampExpressions.map Trace.timestampLookup) := by rfl

theorem range_lookup0
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.PooledRowNative.ShiftBinopUncached.PhysicalAuthoredLookupValid physical) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.ShiftBinopUncached.native.rangeExpression0).Contains (Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.range16Queries.get ⟨0, by decide⟩
  have member := authored.2 query (List.get_mem Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.range16Queries ⟨0, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((physical ∘ Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.ShiftBinopUncached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.ShiftBinopUncached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field5_0.source.value ((physical ∘ Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.ShiftBinopUncached.native.sourcePlacement)] := member nonzero
  have same := (Airbender.Compiler.CleanArgumentsNative.ShiftBinopUncached.native.range_value0 physical data arithmetic)
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.ShiftBinopUncached.native.range16_clean_refinement _ valid _

theorem range_lookup1
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.PooledRowNative.ShiftBinopUncached.PhysicalAuthoredLookupValid physical) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.ShiftBinopUncached.native.rangeExpression1).Contains (Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.range16Queries.get ⟨1, by decide⟩
  have member := authored.2 query (List.get_mem Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.range16Queries ⟨1, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((physical ∘ Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.ShiftBinopUncached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.ShiftBinopUncached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field6_0.source.value ((physical ∘ Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.ShiftBinopUncached.native.sourcePlacement)] := member nonzero
  have same := (Airbender.Compiler.CleanArgumentsNative.ShiftBinopUncached.native.range_value1 physical data arithmetic)
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.ShiftBinopUncached.native.range16_clean_refinement _ valid _

theorem generic_lookup0
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.PooledRowNative.ShiftBinopUncached.PhysicalAuthoredLookupValid physical) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.genericExpressions0).Contains (Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.genericQueries.get ⟨0, by decide⟩
  have member := authored.1 query (List.get_mem Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.genericQueries ⟨0, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((physical ∘ Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.ShiftBinopUncached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.generic_value0_0 physical data arithmetic)
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.generic_value0_1 physical data arithmetic)
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.generic_value0_2 physical data arithmetic)
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.generic_value0_3 physical data arithmetic)
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.generic_value0_4 physical data arithmetic)
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.generic_value0_5 physical data arithmetic)
  have same6 := (Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.generic_value0_6 physical data arithmetic)
  have same7 := (Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.generic_value0_7 physical data arithmetic)
  have same8 := (Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.generic_value0_8 physical data arithmetic)
  have same9 := (Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.generic_value0_9 physical data arithmetic)
  apply clean_vector_lookup
  apply ShiftSetupNative.clean_contains _ ?_ ?_ _
  · simp only [Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.genericExpressions0, Vector.map_mk, List.map_toArray]
    change Airbender.Compiler.MaterializedNative.ShiftBinopUncached.native.model.Contains Airbender.Compiler.TableNative.ShiftBinopUncached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression0_0.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression0_1.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression0_2.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression0_3.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression0_4.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression0_5.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression0_6.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression0_7.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression0_8.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression0_9.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.environment physical data)]
    rw [same0, same1, same2, same3, same4, same5, same6, same7, same8, same9]
    exact valid
  · rw [Vector.getElem_map]
    change Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression0_8.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.environment physical data) = 0
    rw [same8]
    rfl

theorem generic_lookup1
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.PooledRowNative.ShiftBinopUncached.PhysicalAuthoredLookupValid physical) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.genericExpressions1).Contains (Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.genericQueries.get ⟨1, by decide⟩
  have member := authored.1 query (List.get_mem Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.genericQueries ⟨1, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((physical ∘ Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.ShiftBinopUncached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.generic_value1_0 physical data arithmetic)
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.generic_value1_1 physical data arithmetic)
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.generic_value1_2 physical data arithmetic)
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.generic_value1_3 physical data arithmetic)
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.generic_value1_4 physical data arithmetic)
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.generic_value1_5 physical data arithmetic)
  have same6 := (Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.generic_value1_6 physical data arithmetic)
  have same7 := (Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.generic_value1_7 physical data arithmetic)
  have same8 := (Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.generic_value1_8 physical data arithmetic)
  have same9 := (Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.generic_value1_9 physical data arithmetic)
  apply clean_vector_lookup
  apply ShiftSetupNative.clean_contains _ ?_ ?_ _
  · simp only [Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.genericExpressions1, Vector.map_mk, List.map_toArray]
    change Airbender.Compiler.MaterializedNative.ShiftBinopUncached.native.model.Contains Airbender.Compiler.TableNative.ShiftBinopUncached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression1_0.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression1_1.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression1_2.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression1_3.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression1_4.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression1_5.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression1_6.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression1_7.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression1_8.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression1_9.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.environment physical data)]
    rw [same0, same1, same2, same3, same4, same5, same6, same7, same8, same9]
    exact valid
  · rw [Vector.getElem_map]
    change Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression1_8.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.environment physical data) = 0
    rw [same8]
    rfl

theorem generic_lookup2
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.PooledRowNative.ShiftBinopUncached.PhysicalAuthoredLookupValid physical) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.genericExpressions2).Contains (Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.genericQueries.get ⟨2, by decide⟩
  have member := authored.1 query (List.get_mem Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.genericQueries ⟨2, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((physical ∘ Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.ShiftBinopUncached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.generic_value2_0 physical data arithmetic)
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.generic_value2_1 physical data arithmetic)
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.generic_value2_2 physical data arithmetic)
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.generic_value2_3 physical data arithmetic)
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.generic_value2_4 physical data arithmetic)
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.generic_value2_5 physical data arithmetic)
  have same6 := (Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.generic_value2_6 physical data arithmetic)
  have same7 := (Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.generic_value2_7 physical data arithmetic)
  have same8 := (Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.generic_value2_8 physical data arithmetic)
  have same9 := (Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.generic_value2_9 physical data arithmetic)
  apply clean_vector_lookup
  apply ShiftSetupNative.clean_contains _ ?_ ?_ _
  · simp only [Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.genericExpressions2, Vector.map_mk, List.map_toArray]
    change Airbender.Compiler.MaterializedNative.ShiftBinopUncached.native.model.Contains Airbender.Compiler.TableNative.ShiftBinopUncached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression2_0.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression2_1.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression2_2.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression2_3.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression2_4.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression2_5.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression2_6.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression2_7.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression2_8.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression2_9.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.environment physical data)]
    rw [same0, same1, same2, same3, same4, same5, same6, same7, same8, same9]
    exact valid
  · rw [Vector.getElem_map]
    change Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression2_8.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.environment physical data) = 0
    rw [same8]
    rfl

theorem generic_lookup3
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.PooledRowNative.ShiftBinopUncached.PhysicalAuthoredLookupValid physical) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.genericExpressions3).Contains (Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.genericQueries.get ⟨3, by decide⟩
  have member := authored.1 query (List.get_mem Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.genericQueries ⟨3, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((physical ∘ Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.ShiftBinopUncached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.generic_value3_0 physical data arithmetic)
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.generic_value3_1 physical data arithmetic)
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.generic_value3_2 physical data arithmetic)
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.generic_value3_3 physical data arithmetic)
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.generic_value3_4 physical data arithmetic)
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.generic_value3_5 physical data arithmetic)
  have same6 := (Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.generic_value3_6 physical data arithmetic)
  have same7 := (Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.generic_value3_7 physical data arithmetic)
  have same8 := (Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.generic_value3_8 physical data arithmetic)
  have same9 := (Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.generic_value3_9 physical data arithmetic)
  apply clean_vector_lookup
  apply ShiftSetupNative.clean_contains _ ?_ ?_ _
  · simp only [Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.genericExpressions3, Vector.map_mk, List.map_toArray]
    change Airbender.Compiler.MaterializedNative.ShiftBinopUncached.native.model.Contains Airbender.Compiler.TableNative.ShiftBinopUncached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression3_0.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression3_1.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression3_2.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression3_3.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression3_4.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression3_5.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression3_6.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression3_7.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression3_8.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression3_9.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.environment physical data)]
    rw [same0, same1, same2, same3, same4, same5, same6, same7, same8, same9]
    exact valid
  · rw [Vector.getElem_map]
    change Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression3_8.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.environment physical data) = 0
    rw [same8]
    rfl

theorem generic_lookup4
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.PooledRowNative.ShiftBinopUncached.PhysicalAuthoredLookupValid physical) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.genericExpressions4).Contains (Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.genericQueries.get ⟨4, by decide⟩
  have member := authored.1 query (List.get_mem Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.genericQueries ⟨4, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((physical ∘ Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.ShiftBinopUncached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.generic_value4_0 physical data arithmetic)
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.generic_value4_1 physical data arithmetic)
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.generic_value4_2 physical data arithmetic)
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.generic_value4_3 physical data arithmetic)
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.generic_value4_4 physical data arithmetic)
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.generic_value4_5 physical data arithmetic)
  have same6 := (Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.generic_value4_6 physical data arithmetic)
  have same7 := (Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.generic_value4_7 physical data arithmetic)
  have same8 := (Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.generic_value4_8 physical data arithmetic)
  have same9 := (Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.generic_value4_9 physical data arithmetic)
  apply clean_vector_lookup
  apply ShiftSetupNative.clean_contains _ ?_ ?_ _
  · simp only [Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.genericExpressions4, Vector.map_mk, List.map_toArray]
    change Airbender.Compiler.MaterializedNative.ShiftBinopUncached.native.model.Contains Airbender.Compiler.TableNative.ShiftBinopUncached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression4_0.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression4_1.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression4_2.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression4_3.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression4_4.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression4_5.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression4_6.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression4_7.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression4_8.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression4_9.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.environment physical data)]
    rw [same0, same1, same2, same3, same4, same5, same6, same7, same8, same9]
    exact valid
  · rw [Vector.getElem_map]
    change Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression4_8.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.environment physical data) = 0
    rw [same8]
    rfl

theorem retained_clock_from_physical
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank.address) = 0)
    (helpers : ∀ field ∈ Airbender.Compiler.HelperNative.ShiftBinopUncached.native.fields, (field.value (Airbender.Compiler.HelperNative.ShiftBinopUncached.native.sourceValues physical)).val < 524288)
    (authored : Airbender.Compiler.PooledRowNative.ShiftBinopUncached.PhysicalAuthoredLookupValid physical) :
    FlatOperation.ConstraintsHoldFlat (Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.environment physical data) (Airbender.ShiftBinop.clockConstraints (p := babyBearModulus)) := by
  apply Airbender.Compiler.CleanLinksNative.ShiftBinopUncached.retained_clock_constraints physical data arithmetic
  rw [clock_lookup_inventory]
  exact PredicateChecks.all (PredicateChecks.cons (range_lookup0 physical data arithmetic authored) (PredicateChecks.cons (range_lookup1 physical data arithmetic authored) (PredicateChecks.cons (generic_lookup0 physical data arithmetic authored) (PredicateChecks.cons (generic_lookup1 physical data arithmetic authored) (PredicateChecks.cons (generic_lookup2 physical data arithmetic authored) (PredicateChecks.cons (generic_lookup3 physical data arithmetic authored) (PredicateChecks.cons (generic_lookup4 physical data arithmetic authored) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.ShiftBinopUncached.native.timestampExpression0 (Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.ShiftBinopUncached.native.timestamp_bound0 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.ShiftBinopUncached.native.timestampExpression1 (Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.ShiftBinopUncached.native.timestamp_bound1 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.ShiftBinopUncached.native.timestampExpression2 (Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.ShiftBinopUncached.native.timestamp_bound2 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.ShiftBinopUncached.native.timestampExpression3 (Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.ShiftBinopUncached.native.timestamp_bound3 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.ShiftBinopUncached.native.timestampExpression4 (Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.ShiftBinopUncached.native.timestamp_bound4 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.ShiftBinopUncached.native.timestampExpression5 (Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.ShiftBinopUncached.native.timestamp_bound5 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.ShiftBinopUncached.native.timestampExpression6 (Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.ShiftBinopUncached.native.timestamp_bound6 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.ShiftBinopUncached.native.timestampExpression7 (Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.ShiftBinopUncached.native.timestamp_bound7 physical data arithmetic helpers)) PredicateChecks.nil)))))))))))))))

end Airbender.Compiler.PhysicalClosedNative.ShiftBinopUncached
