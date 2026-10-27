import Airbender.Import.Compiler.LogicalRows.UnifiedUncached
import Airbender.Proofs.GKRProtocol.CleanArgumentsNative.UnifiedUncached
import Airbender.Proofs.GKRProtocol.CleanScalarNative.UnifiedUncached
import Airbender.Proofs.GKRProtocol.CleanPrimitiveLookups
import Airbender.Proofs.GKRProtocol.CleanLinksNative.UnifiedUncached
import Airbender.Proofs.GKRProtocol.MaterializedWitnessNative.UnifiedUncached
import Airbender.Proofs.GKRProtocol.CleanGenericArgumentsNative.UnifiedUncached
import Airbender.Proofs.GKRProtocol.CleanGenericSetup

namespace Airbender.Compiler.PhysicalClosedNative.UnifiedUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

noncomputable def nativeSetup : Table Source.BaseField (fields 10) :=
  Airbender.Compiler.MaterializedNative.UnifiedUncached.native.model.imported.data.table "Airbender.Native.UnifiedReduced"

theorem generic_columns_inventory : Airbender.Compiler.TableNative.UnifiedUncached.native.genericSetupColumns =
    (List.range 10).map SourceSetupColumn.generic := by decide +kernel

theorem clock_lookup_inventory :
    FlatOperation.lookups (Airbender.UnifiedReduced.clockConstraints (p := babyBearModulus) nativeSetup) =
    (Airbender.Compiler.CleanArgumentsNative.UnifiedUncached.native.rangeExpressions.map Verification.range16) ++
    (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.genericExpressions.map (fun entry => Lookup.mk nativeSetup.toRaw entry)) ++
    (Airbender.Compiler.CleanArgumentsNative.UnifiedUncached.native.timestampExpressions.map Trace.timestampLookup) := by rfl

theorem range_lookup0
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.UnifiedRowNative.UnifiedUncached.PhysicalAuthoredLookupValid physical) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.UnifiedUncached.native.rangeExpression0).Contains (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.range16Queries.get ⟨0, by decide⟩
  have member := authored.2 query (List.get_mem Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.range16Queries ⟨0, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedUncached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.UnifiedUncached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.UnifiedUncached.native.field5_0.source.value ((physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedUncached.native.sourcePlacement)] := member nonzero
  have same := (Airbender.Compiler.CleanArgumentsNative.UnifiedUncached.native.range_value0 physical data arithmetic)
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.UnifiedUncached.native.range16_clean_refinement _ valid _

theorem range_lookup1
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.UnifiedRowNative.UnifiedUncached.PhysicalAuthoredLookupValid physical) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.UnifiedUncached.native.rangeExpression1).Contains (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.range16Queries.get ⟨1, by decide⟩
  have member := authored.2 query (List.get_mem Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.range16Queries ⟨1, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedUncached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.UnifiedUncached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.UnifiedUncached.native.field6_0.source.value ((physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedUncached.native.sourcePlacement)] := member nonzero
  have same := (Airbender.Compiler.CleanArgumentsNative.UnifiedUncached.native.range_value1 physical data arithmetic)
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.UnifiedUncached.native.range16_clean_refinement _ valid _

theorem range_lookup2
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.UnifiedRowNative.UnifiedUncached.PhysicalAuthoredLookupValid physical) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.UnifiedUncached.native.rangeExpression2).Contains (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.range16Queries.get ⟨2, by decide⟩
  have member := authored.2 query (List.get_mem Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.range16Queries ⟨2, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedUncached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.UnifiedUncached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.UnifiedUncached.native.field7_0.source.value ((physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedUncached.native.sourcePlacement)] := member nonzero
  have same := (Airbender.Compiler.CleanArgumentsNative.UnifiedUncached.native.range_value2 physical data arithmetic)
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.UnifiedUncached.native.range16_clean_refinement _ valid _

theorem range_lookup3
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.UnifiedRowNative.UnifiedUncached.PhysicalAuthoredLookupValid physical) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.UnifiedUncached.native.rangeExpression3).Contains (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.range16Queries.get ⟨3, by decide⟩
  have member := authored.2 query (List.get_mem Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.range16Queries ⟨3, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedUncached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.UnifiedUncached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.UnifiedUncached.native.field8_0.source.value ((physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedUncached.native.sourcePlacement)] := member nonzero
  have same := (Airbender.Compiler.CleanArgumentsNative.UnifiedUncached.native.range_value3 physical data arithmetic)
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.UnifiedUncached.native.range16_clean_refinement _ valid _

theorem range_lookup4
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.UnifiedRowNative.UnifiedUncached.PhysicalAuthoredLookupValid physical) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.UnifiedUncached.native.rangeExpression4).Contains (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.range16Queries.get ⟨4, by decide⟩
  have member := authored.2 query (List.get_mem Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.range16Queries ⟨4, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedUncached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.UnifiedUncached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.UnifiedUncached.native.field9_0.source.value ((physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedUncached.native.sourcePlacement)] := member nonzero
  have same := (Airbender.Compiler.CleanArgumentsNative.UnifiedUncached.native.range_value4 physical data arithmetic)
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.UnifiedUncached.native.range16_clean_refinement _ valid _

theorem range_lookup5
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.UnifiedRowNative.UnifiedUncached.PhysicalAuthoredLookupValid physical) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.UnifiedUncached.native.rangeExpression5).Contains (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.range16Queries.get ⟨5, by decide⟩
  have member := authored.2 query (List.get_mem Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.range16Queries ⟨5, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedUncached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.UnifiedUncached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.UnifiedUncached.native.field10_0.source.value ((physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedUncached.native.sourcePlacement)] := member nonzero
  have same := (Airbender.Compiler.CleanArgumentsNative.UnifiedUncached.native.range_value5 physical data arithmetic)
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.UnifiedUncached.native.range16_clean_refinement _ valid _

theorem range_lookup6
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.UnifiedRowNative.UnifiedUncached.PhysicalAuthoredLookupValid physical) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.UnifiedUncached.native.rangeExpression6).Contains (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.range16Queries.get ⟨6, by decide⟩
  have member := authored.2 query (List.get_mem Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.range16Queries ⟨6, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedUncached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.UnifiedUncached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.UnifiedUncached.native.field11_0.source.value ((physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedUncached.native.sourcePlacement)] := member nonzero
  have same := (Airbender.Compiler.CleanArgumentsNative.UnifiedUncached.native.range_value6 physical data arithmetic)
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.UnifiedUncached.native.range16_clean_refinement _ valid _

theorem range_lookup7
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.UnifiedRowNative.UnifiedUncached.PhysicalAuthoredLookupValid physical) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.UnifiedUncached.native.rangeExpression7).Contains (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.range16Queries.get ⟨7, by decide⟩
  have member := authored.2 query (List.get_mem Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.range16Queries ⟨7, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedUncached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.UnifiedUncached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.UnifiedUncached.native.field12_0.source.value ((physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedUncached.native.sourcePlacement)] := member nonzero
  have same := (Airbender.Compiler.CleanArgumentsNative.UnifiedUncached.native.range_value7 physical data arithmetic)
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.UnifiedUncached.native.range16_clean_refinement _ valid _

theorem range_lookup8
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.UnifiedRowNative.UnifiedUncached.PhysicalAuthoredLookupValid physical) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.UnifiedUncached.native.rangeExpression8).Contains (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.range16Queries.get ⟨8, by decide⟩
  have member := authored.2 query (List.get_mem Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.range16Queries ⟨8, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedUncached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.UnifiedUncached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.UnifiedUncached.native.field13_0.source.value ((physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedUncached.native.sourcePlacement)] := member nonzero
  have same := (Airbender.Compiler.CleanArgumentsNative.UnifiedUncached.native.range_value8 physical data arithmetic)
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.UnifiedUncached.native.range16_clean_refinement _ valid _

theorem range_lookup9
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.UnifiedRowNative.UnifiedUncached.PhysicalAuthoredLookupValid physical) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.UnifiedUncached.native.rangeExpression9).Contains (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.range16Queries.get ⟨9, by decide⟩
  have member := authored.2 query (List.get_mem Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.range16Queries ⟨9, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedUncached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.UnifiedUncached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.UnifiedUncached.native.field14_0.source.value ((physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedUncached.native.sourcePlacement)] := member nonzero
  have same := (Airbender.Compiler.CleanArgumentsNative.UnifiedUncached.native.range_value9 physical data arithmetic)
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.UnifiedUncached.native.range16_clean_refinement _ valid _

theorem range_lookup10
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.UnifiedRowNative.UnifiedUncached.PhysicalAuthoredLookupValid physical) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.UnifiedUncached.native.rangeExpression10).Contains (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.range16Queries.get ⟨10, by decide⟩
  have member := authored.2 query (List.get_mem Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.range16Queries ⟨10, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedUncached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.UnifiedUncached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.UnifiedUncached.native.field15_0.source.value ((physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedUncached.native.sourcePlacement)] := member nonzero
  have same := (Airbender.Compiler.CleanArgumentsNative.UnifiedUncached.native.range_value10 physical data arithmetic)
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.UnifiedUncached.native.range16_clean_refinement _ valid _

theorem range_lookup11
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.UnifiedRowNative.UnifiedUncached.PhysicalAuthoredLookupValid physical) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.UnifiedUncached.native.rangeExpression11).Contains (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.range16Queries.get ⟨11, by decide⟩
  have member := authored.2 query (List.get_mem Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.range16Queries ⟨11, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedUncached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.UnifiedUncached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.UnifiedUncached.native.field16_0.source.value ((physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedUncached.native.sourcePlacement)] := member nonzero
  have same := (Airbender.Compiler.CleanArgumentsNative.UnifiedUncached.native.range_value11 physical data arithmetic)
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.UnifiedUncached.native.range16_clean_refinement _ valid _

theorem range_lookup12
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.UnifiedRowNative.UnifiedUncached.PhysicalAuthoredLookupValid physical) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.UnifiedUncached.native.rangeExpression12).Contains (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.range16Queries.get ⟨12, by decide⟩
  have member := authored.2 query (List.get_mem Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.range16Queries ⟨12, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedUncached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.UnifiedUncached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.UnifiedUncached.native.field17_0.source.value ((physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedUncached.native.sourcePlacement)] := member nonzero
  have same := (Airbender.Compiler.CleanArgumentsNative.UnifiedUncached.native.range_value12 physical data arithmetic)
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.UnifiedUncached.native.range16_clean_refinement _ valid _

theorem generic_lookup0
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.UnifiedRowNative.UnifiedUncached.PhysicalAuthoredLookupValid physical) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.genericExpressions0).Contains (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.genericQueries.get ⟨0, by decide⟩
  have member := authored.1 query (List.get_mem Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.genericQueries ⟨0, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedUncached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.generic_value0_0 physical data arithmetic)
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.generic_value0_1 physical data arithmetic)
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.generic_value0_2 physical data arithmetic)
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.generic_value0_3 physical data arithmetic)
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.generic_value0_4 physical data arithmetic)
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.generic_value0_5 physical data arithmetic)
  have same6 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.generic_value0_6 physical data arithmetic)
  have same7 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.generic_value0_7 physical data arithmetic)
  have same8 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.generic_value0_8 physical data arithmetic)
  have same9 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.generic_value0_9 physical data arithmetic)
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.UnifiedUncached.native.model.generic_clean_contains Airbender.Compiler.TableNative.UnifiedUncached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.UnifiedReduced" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.genericExpressions0, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.UnifiedUncached.native.model.Contains Airbender.Compiler.TableNative.UnifiedUncached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.genericExpression0_0.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.genericExpression0_1.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.genericExpression0_2.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.genericExpression0_3.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.genericExpression0_4.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.genericExpression0_5.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.genericExpression0_6.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.genericExpression0_7.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.genericExpression0_8.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.genericExpression0_9.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5, same6, same7, same8, same9]
  exact valid

theorem generic_lookup1
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.UnifiedRowNative.UnifiedUncached.PhysicalAuthoredLookupValid physical) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.genericExpressions1).Contains (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.genericQueries.get ⟨1, by decide⟩
  have member := authored.1 query (List.get_mem Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.genericQueries ⟨1, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedUncached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.generic_value1_0 physical data arithmetic)
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.generic_value1_1 physical data arithmetic)
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.generic_value1_2 physical data arithmetic)
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.generic_value1_3 physical data arithmetic)
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.generic_value1_4 physical data arithmetic)
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.generic_value1_5 physical data arithmetic)
  have same6 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.generic_value1_6 physical data arithmetic)
  have same7 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.generic_value1_7 physical data arithmetic)
  have same8 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.generic_value1_8 physical data arithmetic)
  have same9 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.generic_value1_9 physical data arithmetic)
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.UnifiedUncached.native.model.generic_clean_contains Airbender.Compiler.TableNative.UnifiedUncached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.UnifiedReduced" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.genericExpressions1, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.UnifiedUncached.native.model.Contains Airbender.Compiler.TableNative.UnifiedUncached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.genericExpression1_0.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.genericExpression1_1.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.genericExpression1_2.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.genericExpression1_3.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.genericExpression1_4.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.genericExpression1_5.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.genericExpression1_6.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.genericExpression1_7.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.genericExpression1_8.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.genericExpression1_9.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5, same6, same7, same8, same9]
  exact valid

theorem generic_lookup2
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.UnifiedRowNative.UnifiedUncached.PhysicalAuthoredLookupValid physical) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.genericExpressions2).Contains (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.genericQueries.get ⟨2, by decide⟩
  have member := authored.1 query (List.get_mem Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.genericQueries ⟨2, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedUncached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.generic_value2_0 physical data arithmetic)
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.generic_value2_1 physical data arithmetic)
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.generic_value2_2 physical data arithmetic)
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.generic_value2_3 physical data arithmetic)
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.generic_value2_4 physical data arithmetic)
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.generic_value2_5 physical data arithmetic)
  have same6 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.generic_value2_6 physical data arithmetic)
  have same7 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.generic_value2_7 physical data arithmetic)
  have same8 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.generic_value2_8 physical data arithmetic)
  have same9 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.generic_value2_9 physical data arithmetic)
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.UnifiedUncached.native.model.generic_clean_contains Airbender.Compiler.TableNative.UnifiedUncached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.UnifiedReduced" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.genericExpressions2, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.UnifiedUncached.native.model.Contains Airbender.Compiler.TableNative.UnifiedUncached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.genericExpression2_0.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.genericExpression2_1.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.genericExpression2_2.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.genericExpression2_3.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.genericExpression2_4.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.genericExpression2_5.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.genericExpression2_6.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.genericExpression2_7.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.genericExpression2_8.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.genericExpression2_9.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5, same6, same7, same8, same9]
  exact valid

theorem generic_lookup3
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.UnifiedRowNative.UnifiedUncached.PhysicalAuthoredLookupValid physical) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.genericExpressions3).Contains (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.genericQueries.get ⟨3, by decide⟩
  have member := authored.1 query (List.get_mem Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.genericQueries ⟨3, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedUncached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.generic_value3_0 physical data arithmetic)
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.generic_value3_1 physical data arithmetic)
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.generic_value3_2 physical data arithmetic)
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.generic_value3_3 physical data arithmetic)
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.generic_value3_4 physical data arithmetic)
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.generic_value3_5 physical data arithmetic)
  have same6 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.generic_value3_6 physical data arithmetic)
  have same7 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.generic_value3_7 physical data arithmetic)
  have same8 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.generic_value3_8 physical data arithmetic)
  have same9 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.generic_value3_9 physical data arithmetic)
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.UnifiedUncached.native.model.generic_clean_contains Airbender.Compiler.TableNative.UnifiedUncached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.UnifiedReduced" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.genericExpressions3, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.UnifiedUncached.native.model.Contains Airbender.Compiler.TableNative.UnifiedUncached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.genericExpression3_0.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.genericExpression3_1.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.genericExpression3_2.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.genericExpression3_3.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.genericExpression3_4.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.genericExpression3_5.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.genericExpression3_6.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.genericExpression3_7.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.genericExpression3_8.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.genericExpression3_9.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5, same6, same7, same8, same9]
  exact valid

theorem generic_lookup4
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.UnifiedRowNative.UnifiedUncached.PhysicalAuthoredLookupValid physical) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.genericExpressions4).Contains (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.genericQueries.get ⟨4, by decide⟩
  have member := authored.1 query (List.get_mem Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.genericQueries ⟨4, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedUncached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.generic_value4_0 physical data arithmetic)
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.generic_value4_1 physical data arithmetic)
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.generic_value4_2 physical data arithmetic)
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.generic_value4_3 physical data arithmetic)
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.generic_value4_4 physical data arithmetic)
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.generic_value4_5 physical data arithmetic)
  have same6 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.generic_value4_6 physical data arithmetic)
  have same7 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.generic_value4_7 physical data arithmetic)
  have same8 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.generic_value4_8 physical data arithmetic)
  have same9 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.generic_value4_9 physical data arithmetic)
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.UnifiedUncached.native.model.generic_clean_contains Airbender.Compiler.TableNative.UnifiedUncached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.UnifiedReduced" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.genericExpressions4, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.UnifiedUncached.native.model.Contains Airbender.Compiler.TableNative.UnifiedUncached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.genericExpression4_0.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.genericExpression4_1.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.genericExpression4_2.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.genericExpression4_3.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.genericExpression4_4.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.genericExpression4_5.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.genericExpression4_6.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.genericExpression4_7.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.genericExpression4_8.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.genericExpression4_9.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5, same6, same7, same8, same9]
  exact valid

theorem retained_clock_from_physical
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.bank.address) = 0)
    (helpers : ∀ field ∈ Airbender.Compiler.HelperNative.UnifiedUncached.native.fields, (field.value (Airbender.Compiler.HelperNative.UnifiedUncached.native.sourceValues physical)).val < 524288)
    (authored : Airbender.Compiler.UnifiedRowNative.UnifiedUncached.PhysicalAuthoredLookupValid physical) :
    FlatOperation.ConstraintsHoldFlat (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment physical data) (Airbender.UnifiedReduced.clockConstraints (p := babyBearModulus) nativeSetup) := by
  apply Airbender.Compiler.CleanLinksNative.UnifiedUncached.retained_clock_constraints nativeSetup physical data arithmetic
  rw [clock_lookup_inventory]
  exact PredicateChecks.all (PredicateChecks.cons (range_lookup0 physical data arithmetic authored) (PredicateChecks.cons (range_lookup1 physical data arithmetic authored) (PredicateChecks.cons (range_lookup2 physical data arithmetic authored) (PredicateChecks.cons (range_lookup3 physical data arithmetic authored) (PredicateChecks.cons (range_lookup4 physical data arithmetic authored) (PredicateChecks.cons (range_lookup5 physical data arithmetic authored) (PredicateChecks.cons (range_lookup6 physical data arithmetic authored) (PredicateChecks.cons (range_lookup7 physical data arithmetic authored) (PredicateChecks.cons (range_lookup8 physical data arithmetic authored) (PredicateChecks.cons (range_lookup9 physical data arithmetic authored) (PredicateChecks.cons (range_lookup10 physical data arithmetic authored) (PredicateChecks.cons (range_lookup11 physical data arithmetic authored) (PredicateChecks.cons (range_lookup12 physical data arithmetic authored) (PredicateChecks.cons (generic_lookup0 physical data arithmetic authored) (PredicateChecks.cons (generic_lookup1 physical data arithmetic authored) (PredicateChecks.cons (generic_lookup2 physical data arithmetic authored) (PredicateChecks.cons (generic_lookup3 physical data arithmetic authored) (PredicateChecks.cons (generic_lookup4 physical data arithmetic authored) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.UnifiedUncached.native.timestampExpression0 (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.UnifiedUncached.native.timestamp_bound0 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.UnifiedUncached.native.timestampExpression1 (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.UnifiedUncached.native.timestamp_bound1 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.UnifiedUncached.native.timestampExpression2 (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.UnifiedUncached.native.timestamp_bound2 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.UnifiedUncached.native.timestampExpression3 (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.UnifiedUncached.native.timestamp_bound3 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.UnifiedUncached.native.timestampExpression4 (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.UnifiedUncached.native.timestamp_bound4 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.UnifiedUncached.native.timestampExpression5 (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.UnifiedUncached.native.timestamp_bound5 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.UnifiedUncached.native.timestampExpression6 (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.UnifiedUncached.native.timestamp_bound6 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.UnifiedUncached.native.timestampExpression7 (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.UnifiedUncached.native.timestamp_bound7 physical data arithmetic helpers)) PredicateChecks.nil))))))))))))))))))))))))))

end Airbender.Compiler.PhysicalClosedNative.UnifiedUncached
