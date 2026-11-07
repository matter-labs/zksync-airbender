import Airbender.Import.Compiler.LogicalRows.JumpBranchCached
import Airbender.Proofs.GKRProtocol.CleanArgumentsNative.JumpBranchCached
import Airbender.Proofs.GKRProtocol.CleanScalarNative.JumpBranchCached
import Airbender.Proofs.GKRProtocol.CleanGenericArgumentsNative.JumpBranchCached
import Airbender.Proofs.GKRProtocol.FixedPrimitives
import Airbender.Proofs.GKRProtocol.FixedSetupNative.JumpBranchMembership
import Airbender.Proofs.GKRProtocol.CleanLinksNative.JumpBranchCached
import Airbender.Proofs.GKRProtocol.MaterializedWitnessNative.JumpBranchCached
import Airbender.Proofs.Constraints

namespace Airbender.Compiler.PhysicalClosedNative.JumpBranchCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

noncomputable def fixedLookup0 : Lookup Source.BaseField :=
  Verification.pairLookup Verification.regIsZeroTable Airbender.Compiler.CleanGenericArgumentsNative.JumpBranchCached.native.part0.genericExpression0_0 Airbender.Compiler.CleanGenericArgumentsNative.JumpBranchCached.native.part0.genericExpression0_1

noncomputable def fixedLookup1 : Lookup Source.BaseField :=
  Verification.pairLookup Verification.u16SignTable Airbender.Compiler.CleanGenericArgumentsNative.JumpBranchCached.native.part0.genericExpression1_0 Airbender.Compiler.CleanGenericArgumentsNative.JumpBranchCached.native.part0.genericExpression1_1

noncomputable def fixedLookup2 : Lookup Source.BaseField :=
  Verification.pairLookup Verification.conditionalTable Airbender.Compiler.CleanGenericArgumentsNative.JumpBranchCached.native.part0.genericExpression2_0 Airbender.Compiler.CleanGenericArgumentsNative.JumpBranchCached.native.part0.genericExpression2_1

noncomputable def fixedLookup3 : Lookup Source.BaseField :=
  Verification.jumpCleanup Airbender.Compiler.CleanGenericArgumentsNative.JumpBranchCached.native.part0.genericExpression3_0 Airbender.Compiler.CleanGenericArgumentsNative.JumpBranchCached.native.part0.genericExpression3_1 Airbender.Compiler.CleanGenericArgumentsNative.JumpBranchCached.native.part0.genericExpression3_2

noncomputable def fixedLookups : List (Lookup Source.BaseField) := [fixedLookup0, fixedLookup1, fixedLookup2, fixedLookup3]

theorem clock_lookup_inventory :
    FlatOperation.lookups (Airbender.JumpBranchSlt.clockConstraints (p := babyBearModulus)) =
    (Airbender.Compiler.CleanArgumentsNative.JumpBranchCached.native.rangeExpressions.map Verification.range16) ++ fixedLookups ++
      (Airbender.Compiler.CleanArgumentsNative.JumpBranchCached.native.timestampExpressions.map Trace.timestampLookup) := by rfl

theorem range_lookup0
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.PooledRowNative.JumpBranchCached.PhysicalAuthoredLookupValid physical) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.JumpBranchCached.native.rangeExpression0).Contains (Airbender.Compiler.CleanArithmeticNative.JumpBranchCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.range16Queries.get ⟨0, by decide⟩
  have member := authored.2 query (List.get_mem Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.range16Queries ⟨0, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((physical ∘ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.JumpBranchCached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.JumpBranchCached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.JumpBranchCached.native.field4_0.source.value ((physical ∘ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.JumpBranchCached.native.sourcePlacement)] := member nonzero
  have same := (Airbender.Compiler.CleanArgumentsNative.JumpBranchCached.native.range_value0 physical data arithmetic)
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.JumpBranchCached.native.range16_clean_refinement _ valid _

theorem range_lookup1
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.PooledRowNative.JumpBranchCached.PhysicalAuthoredLookupValid physical) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.JumpBranchCached.native.rangeExpression1).Contains (Airbender.Compiler.CleanArithmeticNative.JumpBranchCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.range16Queries.get ⟨1, by decide⟩
  have member := authored.2 query (List.get_mem Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.range16Queries ⟨1, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((physical ∘ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.JumpBranchCached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.JumpBranchCached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.JumpBranchCached.native.field5_0.source.value ((physical ∘ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.JumpBranchCached.native.sourcePlacement)] := member nonzero
  have same := (Airbender.Compiler.CleanArgumentsNative.JumpBranchCached.native.range_value1 physical data arithmetic)
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.JumpBranchCached.native.range16_clean_refinement _ valid _

theorem range_lookup2
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.PooledRowNative.JumpBranchCached.PhysicalAuthoredLookupValid physical) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.JumpBranchCached.native.rangeExpression2).Contains (Airbender.Compiler.CleanArithmeticNative.JumpBranchCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.range16Queries.get ⟨2, by decide⟩
  have member := authored.2 query (List.get_mem Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.range16Queries ⟨2, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((physical ∘ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.JumpBranchCached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.JumpBranchCached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.JumpBranchCached.native.field6_0.source.value ((physical ∘ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.JumpBranchCached.native.sourcePlacement)] := member nonzero
  have same := (Airbender.Compiler.CleanArgumentsNative.JumpBranchCached.native.range_value2 physical data arithmetic)
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.JumpBranchCached.native.range16_clean_refinement _ valid _

theorem range_lookup3
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.PooledRowNative.JumpBranchCached.PhysicalAuthoredLookupValid physical) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.JumpBranchCached.native.rangeExpression3).Contains (Airbender.Compiler.CleanArithmeticNative.JumpBranchCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.range16Queries.get ⟨3, by decide⟩
  have member := authored.2 query (List.get_mem Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.range16Queries ⟨3, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((physical ∘ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.JumpBranchCached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.JumpBranchCached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.JumpBranchCached.native.field7_0.source.value ((physical ∘ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.JumpBranchCached.native.sourcePlacement)] := member nonzero
  have same := (Airbender.Compiler.CleanArgumentsNative.JumpBranchCached.native.range_value3 physical data arithmetic)
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.JumpBranchCached.native.range16_clean_refinement _ valid _

theorem generic_lookup0
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.PooledRowNative.JumpBranchCached.PhysicalAuthoredLookupValid physical) :
    fixedLookup0.Contains (Airbender.Compiler.CleanArithmeticNative.JumpBranchCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.genericQueries.get ⟨0, by decide⟩
  have member := authored.1 query (List.get_mem Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.genericQueries ⟨0, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((physical ∘ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.JumpBranchCached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  obtain ⟨setupRow, dataRow⟩ := member nonzero
  have tagProof := congrArg (fun entries : List Source.BaseField => entries.getD 9 0) dataRow
  change (1 : Source.BaseField) = Airbender.Compiler.MaterializedNative.JumpBranchCached.native.model.value setupRow (.generic 9) at tagProof
  have selected : Airbender.Compiler.FixedSetupNative.JumpBranch.nativeSetup.value setupRow (.generic 9) = 1 := tagProof.symm
  have sourceCell0 := congrArg (fun entries : List Source.BaseField => entries.getD 0 0) dataRow
  change Airbender.Compiler.LookupNative.JumpBranchCached.native.field0_0.source.value ((physical ∘ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.JumpBranchCached.native.sourcePlacement) = Airbender.Compiler.MaterializedNative.JumpBranchCached.native.model.value setupRow (.generic 0) at sourceCell0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.JumpBranchCached.native.part0.generic_value0_0 physical data arithmetic).trans sourceCell0
  have sourceCell1 := congrArg (fun entries : List Source.BaseField => entries.getD 1 0) dataRow
  change Airbender.Compiler.LookupNative.JumpBranchCached.native.field0_1.source.value ((physical ∘ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.JumpBranchCached.native.sourcePlacement) = Airbender.Compiler.MaterializedNative.JumpBranchCached.native.model.value setupRow (.generic 1) at sourceCell1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.JumpBranchCached.native.part0.generic_value0_1 physical data arithmetic).trans sourceCell1
  apply clean_pair_lookup
  rw [same0, same1]
  exact Airbender.Compiler.FixedSetupNative.JumpBranch.tag1_contains setupRow selected _

theorem generic_lookup1
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.PooledRowNative.JumpBranchCached.PhysicalAuthoredLookupValid physical) :
    fixedLookup1.Contains (Airbender.Compiler.CleanArithmeticNative.JumpBranchCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.genericQueries.get ⟨1, by decide⟩
  have member := authored.1 query (List.get_mem Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.genericQueries ⟨1, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((physical ∘ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.JumpBranchCached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  obtain ⟨setupRow, dataRow⟩ := member nonzero
  have tagProof := congrArg (fun entries : List Source.BaseField => entries.getD 9 0) dataRow
  change (5 : Source.BaseField) = Airbender.Compiler.MaterializedNative.JumpBranchCached.native.model.value setupRow (.generic 9) at tagProof
  have selected : Airbender.Compiler.FixedSetupNative.JumpBranch.nativeSetup.value setupRow (.generic 9) = 5 := tagProof.symm
  have sourceCell0 := congrArg (fun entries : List Source.BaseField => entries.getD 0 0) dataRow
  change Airbender.Compiler.LookupNative.JumpBranchCached.native.field1_0.source.value ((physical ∘ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.JumpBranchCached.native.sourcePlacement) = Airbender.Compiler.MaterializedNative.JumpBranchCached.native.model.value setupRow (.generic 0) at sourceCell0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.JumpBranchCached.native.part0.generic_value1_0 physical data arithmetic).trans sourceCell0
  have sourceCell1 := congrArg (fun entries : List Source.BaseField => entries.getD 1 0) dataRow
  change Airbender.Compiler.LookupNative.JumpBranchCached.native.field1_1.source.value ((physical ∘ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.JumpBranchCached.native.sourcePlacement) = Airbender.Compiler.MaterializedNative.JumpBranchCached.native.model.value setupRow (.generic 1) at sourceCell1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.JumpBranchCached.native.part0.generic_value1_1 physical data arithmetic).trans sourceCell1
  apply clean_pair_lookup
  rw [same0, same1]
  exact Airbender.Compiler.FixedSetupNative.JumpBranch.tag5_contains setupRow selected _

theorem generic_lookup2
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.PooledRowNative.JumpBranchCached.PhysicalAuthoredLookupValid physical) :
    fixedLookup2.Contains (Airbender.Compiler.CleanArithmeticNative.JumpBranchCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.genericQueries.get ⟨2, by decide⟩
  have member := authored.1 query (List.get_mem Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.genericQueries ⟨2, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((physical ∘ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.JumpBranchCached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  obtain ⟨setupRow, dataRow⟩ := member nonzero
  have tagProof := congrArg (fun entries : List Source.BaseField => entries.getD 9 0) dataRow
  change (31 : Source.BaseField) = Airbender.Compiler.MaterializedNative.JumpBranchCached.native.model.value setupRow (.generic 9) at tagProof
  have selected : Airbender.Compiler.FixedSetupNative.JumpBranch.nativeSetup.value setupRow (.generic 9) = 31 := tagProof.symm
  have sourceCell0 := congrArg (fun entries : List Source.BaseField => entries.getD 0 0) dataRow
  change Airbender.Compiler.LookupNative.JumpBranchCached.native.field2_0.source.value ((physical ∘ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.JumpBranchCached.native.sourcePlacement) = Airbender.Compiler.MaterializedNative.JumpBranchCached.native.model.value setupRow (.generic 0) at sourceCell0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.JumpBranchCached.native.part0.generic_value2_0 physical data arithmetic).trans sourceCell0
  have sourceCell1 := congrArg (fun entries : List Source.BaseField => entries.getD 1 0) dataRow
  change Airbender.Compiler.LookupNative.JumpBranchCached.native.field2_1.source.value ((physical ∘ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.JumpBranchCached.native.sourcePlacement) = Airbender.Compiler.MaterializedNative.JumpBranchCached.native.model.value setupRow (.generic 1) at sourceCell1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.JumpBranchCached.native.part0.generic_value2_1 physical data arithmetic).trans sourceCell1
  apply clean_pair_lookup
  rw [same0, same1]
  exact Airbender.Compiler.FixedSetupNative.JumpBranch.tag31_contains setupRow selected _

theorem generic_lookup3
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.PooledRowNative.JumpBranchCached.PhysicalAuthoredLookupValid physical) :
    fixedLookup3.Contains (Airbender.Compiler.CleanArithmeticNative.JumpBranchCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.genericQueries.get ⟨3, by decide⟩
  have member := authored.1 query (List.get_mem Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.genericQueries ⟨3, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((physical ∘ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.JumpBranchCached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  obtain ⟨setupRow, dataRow⟩ := member nonzero
  have tagProof := congrArg (fun entries : List Source.BaseField => entries.getD 9 0) dataRow
  change (2 : Source.BaseField) = Airbender.Compiler.MaterializedNative.JumpBranchCached.native.model.value setupRow (.generic 9) at tagProof
  have selected : Airbender.Compiler.FixedSetupNative.JumpBranch.nativeSetup.value setupRow (.generic 9) = 2 := tagProof.symm
  have sourceCell0 := congrArg (fun entries : List Source.BaseField => entries.getD 0 0) dataRow
  change Airbender.Compiler.LookupNative.JumpBranchCached.native.field3_0.source.value ((physical ∘ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.JumpBranchCached.native.sourcePlacement) = Airbender.Compiler.MaterializedNative.JumpBranchCached.native.model.value setupRow (.generic 0) at sourceCell0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.JumpBranchCached.native.part0.generic_value3_0 physical data arithmetic).trans sourceCell0
  have sourceCell1 := congrArg (fun entries : List Source.BaseField => entries.getD 1 0) dataRow
  change Airbender.Compiler.LookupNative.JumpBranchCached.native.field3_1.source.value ((physical ∘ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.JumpBranchCached.native.sourcePlacement) = Airbender.Compiler.MaterializedNative.JumpBranchCached.native.model.value setupRow (.generic 1) at sourceCell1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.JumpBranchCached.native.part0.generic_value3_1 physical data arithmetic).trans sourceCell1
  have sourceCell2 := congrArg (fun entries : List Source.BaseField => entries.getD 2 0) dataRow
  change Airbender.Compiler.LookupNative.JumpBranchCached.native.field3_2.source.value ((physical ∘ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.JumpBranchCached.native.sourcePlacement) = Airbender.Compiler.MaterializedNative.JumpBranchCached.native.model.value setupRow (.generic 2) at sourceCell2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.JumpBranchCached.native.part0.generic_value3_2 physical data arithmetic).trans sourceCell2
  apply clean_triple_lookup
  rw [same0, same1, same2]
  exact Airbender.Compiler.FixedSetupNative.JumpBranch.tag2_contains setupRow selected _

theorem retained_clock_from_physical
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.bank.address) = 0)
    (helpers : ∀ field ∈ Airbender.Compiler.HelperNative.JumpBranchCached.native.fields, (field.value (Airbender.Compiler.HelperNative.JumpBranchCached.native.sourceValues physical)).val < 524288)
    (authored : Airbender.Compiler.PooledRowNative.JumpBranchCached.PhysicalAuthoredLookupValid physical) :
    FlatOperation.ConstraintsHoldFlat (Airbender.Compiler.CleanArithmeticNative.JumpBranchCached.native.environment physical data) (Airbender.JumpBranchSlt.clockConstraints (p := babyBearModulus)) := by
  apply Airbender.Compiler.CleanLinksNative.JumpBranchCached.retained_clock_constraints physical data arithmetic
  rw [clock_lookup_inventory]
  exact PredicateChecks.all (PredicateChecks.cons (range_lookup0 physical data arithmetic authored) (PredicateChecks.cons (range_lookup1 physical data arithmetic authored) (PredicateChecks.cons (range_lookup2 physical data arithmetic authored) (PredicateChecks.cons (range_lookup3 physical data arithmetic authored) (PredicateChecks.cons (generic_lookup0 physical data arithmetic authored) (PredicateChecks.cons (generic_lookup1 physical data arithmetic authored) (PredicateChecks.cons (generic_lookup2 physical data arithmetic authored) (PredicateChecks.cons (generic_lookup3 physical data arithmetic authored) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.JumpBranchCached.native.timestampExpression0 (Airbender.Compiler.CleanArithmeticNative.JumpBranchCached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.JumpBranchCached.native.timestamp_bound0 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.JumpBranchCached.native.timestampExpression1 (Airbender.Compiler.CleanArithmeticNative.JumpBranchCached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.JumpBranchCached.native.timestamp_bound1 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.JumpBranchCached.native.timestampExpression2 (Airbender.Compiler.CleanArithmeticNative.JumpBranchCached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.JumpBranchCached.native.timestamp_bound2 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.JumpBranchCached.native.timestampExpression3 (Airbender.Compiler.CleanArithmeticNative.JumpBranchCached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.JumpBranchCached.native.timestamp_bound3 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.JumpBranchCached.native.timestampExpression4 (Airbender.Compiler.CleanArithmeticNative.JumpBranchCached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.JumpBranchCached.native.timestamp_bound4 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.JumpBranchCached.native.timestampExpression5 (Airbender.Compiler.CleanArithmeticNative.JumpBranchCached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.JumpBranchCached.native.timestamp_bound5 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.JumpBranchCached.native.timestampExpression6 (Airbender.Compiler.CleanArithmeticNative.JumpBranchCached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.JumpBranchCached.native.timestamp_bound6 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.JumpBranchCached.native.timestampExpression7 (Airbender.Compiler.CleanArithmeticNative.JumpBranchCached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.JumpBranchCached.native.timestamp_bound7 physical data arithmetic helpers)) PredicateChecks.nil))))))))))))))))

end Airbender.Compiler.PhysicalClosedNative.JumpBranchCached
