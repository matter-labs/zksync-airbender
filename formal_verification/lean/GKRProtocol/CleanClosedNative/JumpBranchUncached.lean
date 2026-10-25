import GKRProtocol.CleanArgumentsNative.JumpBranchUncached
import GKRProtocol.CleanScalarNative.JumpBranchUncached
import GKRProtocol.CleanGenericArgumentsNative.JumpBranchUncached
import GKRProtocol.FixedPrimitives
import GKRProtocol.FixedSetupNative.JumpBranchMembership
import GKRProtocol.CleanLinksNative.JumpBranchUncached
import GKRProtocol.MaterializedWitnessNative.JumpBranchUncached
import Airbender.Proofs.Constraints

namespace Airbender.Compiler.CleanClosedNative.JumpBranchUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

noncomputable def fixedLookup0 : Lookup Source.BaseField :=
  Verification.pairLookup Verification.regIsZeroTable Airbender.Compiler.CleanGenericArgumentsNative.JumpBranchUncached.native.part0.genericExpression0_0 Airbender.Compiler.CleanGenericArgumentsNative.JumpBranchUncached.native.part0.genericExpression0_1

noncomputable def fixedLookup1 : Lookup Source.BaseField :=
  Verification.pairLookup Verification.u16SignTable Airbender.Compiler.CleanGenericArgumentsNative.JumpBranchUncached.native.part0.genericExpression1_0 Airbender.Compiler.CleanGenericArgumentsNative.JumpBranchUncached.native.part0.genericExpression1_1

noncomputable def fixedLookup2 : Lookup Source.BaseField :=
  Verification.pairLookup Verification.conditionalTable Airbender.Compiler.CleanGenericArgumentsNative.JumpBranchUncached.native.part0.genericExpression2_0 Airbender.Compiler.CleanGenericArgumentsNative.JumpBranchUncached.native.part0.genericExpression2_1

noncomputable def fixedLookup3 : Lookup Source.BaseField :=
  Verification.jumpCleanup Airbender.Compiler.CleanGenericArgumentsNative.JumpBranchUncached.native.part0.genericExpression3_0 Airbender.Compiler.CleanGenericArgumentsNative.JumpBranchUncached.native.part0.genericExpression3_1 Airbender.Compiler.CleanGenericArgumentsNative.JumpBranchUncached.native.part0.genericExpression3_2

noncomputable def fixedLookups : List (Lookup Source.BaseField) := [fixedLookup0, fixedLookup1, fixedLookup2, fixedLookup3]

theorem clock_lookup_inventory :
    FlatOperation.lookups (Airbender.JumpBranchSlt.clockConstraints (p := babyBearModulus)) =
    (Airbender.Compiler.CleanArgumentsNative.JumpBranchUncached.native.rangeExpressions.map Verification.range16) ++ fixedLookups ++
      (Airbender.Compiler.CleanArgumentsNative.JumpBranchUncached.native.timestampExpressions.map Trace.timestampLookup) := by rfl

theorem range_lookup0
    (sourceValue : Fin 55 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.JumpBranchUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.JumpBranchUncached.native.assigned (Airbender.Compiler.HelperValidityNative.JumpBranchUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.JumpBranchUncached.AuthoredLookupValid sourceValue) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.JumpBranchUncached.native.rangeExpression0).Contains (Airbender.Compiler.CleanArithmeticNative.JumpBranchUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.JumpBranchUncached.native.range16Queries.get ⟨0, by decide⟩
  have member := authored.2 query (List.get_mem Airbender.Compiler.LookupSourceNative.JumpBranchUncached.native.range16Queries ⟨0, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.JumpBranchUncached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.JumpBranchUncached.native.field4_0.source.value (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.originalProjection)] := member nonzero
  have present : Airbender.Compiler.LookupNative.JumpBranchUncached.native.field4_0.source ∈ Airbender.Compiler.QueryFrameNative.JumpBranchUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.JumpBranchUncached.native.fields ⟨51, by decide⟩
  have transported := Airbender.Compiler.QueryFrameNative.JumpBranchUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.JumpBranchUncached.native.field4_0.source present
  have same := (Airbender.Compiler.CleanArgumentsNative.JumpBranchUncached.native.range_value0 physical data arithmetic).trans transported
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.JumpBranchUncached.native.range16_clean_refinement _ valid _

theorem range_lookup1
    (sourceValue : Fin 55 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.JumpBranchUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.JumpBranchUncached.native.assigned (Airbender.Compiler.HelperValidityNative.JumpBranchUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.JumpBranchUncached.AuthoredLookupValid sourceValue) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.JumpBranchUncached.native.rangeExpression1).Contains (Airbender.Compiler.CleanArithmeticNative.JumpBranchUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.JumpBranchUncached.native.range16Queries.get ⟨1, by decide⟩
  have member := authored.2 query (List.get_mem Airbender.Compiler.LookupSourceNative.JumpBranchUncached.native.range16Queries ⟨1, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.JumpBranchUncached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.JumpBranchUncached.native.field5_0.source.value (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.originalProjection)] := member nonzero
  have present : Airbender.Compiler.LookupNative.JumpBranchUncached.native.field5_0.source ∈ Airbender.Compiler.QueryFrameNative.JumpBranchUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.JumpBranchUncached.native.fields ⟨52, by decide⟩
  have transported := Airbender.Compiler.QueryFrameNative.JumpBranchUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.JumpBranchUncached.native.field5_0.source present
  have same := (Airbender.Compiler.CleanArgumentsNative.JumpBranchUncached.native.range_value1 physical data arithmetic).trans transported
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.JumpBranchUncached.native.range16_clean_refinement _ valid _

theorem range_lookup2
    (sourceValue : Fin 55 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.JumpBranchUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.JumpBranchUncached.native.assigned (Airbender.Compiler.HelperValidityNative.JumpBranchUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.JumpBranchUncached.AuthoredLookupValid sourceValue) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.JumpBranchUncached.native.rangeExpression2).Contains (Airbender.Compiler.CleanArithmeticNative.JumpBranchUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.JumpBranchUncached.native.range16Queries.get ⟨2, by decide⟩
  have member := authored.2 query (List.get_mem Airbender.Compiler.LookupSourceNative.JumpBranchUncached.native.range16Queries ⟨2, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.JumpBranchUncached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.JumpBranchUncached.native.field6_0.source.value (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.originalProjection)] := member nonzero
  have present : Airbender.Compiler.LookupNative.JumpBranchUncached.native.field6_0.source ∈ Airbender.Compiler.QueryFrameNative.JumpBranchUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.JumpBranchUncached.native.fields ⟨53, by decide⟩
  have transported := Airbender.Compiler.QueryFrameNative.JumpBranchUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.JumpBranchUncached.native.field6_0.source present
  have same := (Airbender.Compiler.CleanArgumentsNative.JumpBranchUncached.native.range_value2 physical data arithmetic).trans transported
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.JumpBranchUncached.native.range16_clean_refinement _ valid _

theorem range_lookup3
    (sourceValue : Fin 55 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.JumpBranchUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.JumpBranchUncached.native.assigned (Airbender.Compiler.HelperValidityNative.JumpBranchUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.JumpBranchUncached.AuthoredLookupValid sourceValue) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.JumpBranchUncached.native.rangeExpression3).Contains (Airbender.Compiler.CleanArithmeticNative.JumpBranchUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.JumpBranchUncached.native.range16Queries.get ⟨3, by decide⟩
  have member := authored.2 query (List.get_mem Airbender.Compiler.LookupSourceNative.JumpBranchUncached.native.range16Queries ⟨3, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.JumpBranchUncached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.JumpBranchUncached.native.field7_0.source.value (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.originalProjection)] := member nonzero
  have present : Airbender.Compiler.LookupNative.JumpBranchUncached.native.field7_0.source ∈ Airbender.Compiler.QueryFrameNative.JumpBranchUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.JumpBranchUncached.native.fields ⟨54, by decide⟩
  have transported := Airbender.Compiler.QueryFrameNative.JumpBranchUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.JumpBranchUncached.native.field7_0.source present
  have same := (Airbender.Compiler.CleanArgumentsNative.JumpBranchUncached.native.range_value3 physical data arithmetic).trans transported
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.JumpBranchUncached.native.range16_clean_refinement _ valid _

theorem generic_lookup0
    (sourceValue : Fin 55 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.JumpBranchUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.JumpBranchUncached.native.assigned (Airbender.Compiler.HelperValidityNative.JumpBranchUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.JumpBranchUncached.AuthoredLookupValid sourceValue) :
    fixedLookup0.Contains (Airbender.Compiler.CleanArithmeticNative.JumpBranchUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.JumpBranchUncached.native.genericQueries.get ⟨0, by decide⟩
  have member := authored.1 query (List.get_mem Airbender.Compiler.LookupSourceNative.JumpBranchUncached.native.genericQueries ⟨0, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  obtain ⟨setupRow, dataRow⟩ := member nonzero
  have tagProof := congrArg (fun entries : List Source.BaseField => entries.getD 9 0) dataRow
  change (1 : Source.BaseField) = Airbender.Compiler.MaterializedNative.JumpBranchUncached.native.model.value setupRow (.generic 9) at tagProof
  have selected : Airbender.Compiler.FixedSetupNative.JumpBranch.nativeSetup.value setupRow (.generic 9) = 1 := tagProof.symm
  have present0 : Airbender.Compiler.LookupNative.JumpBranchUncached.native.field0_0.source ∈ Airbender.Compiler.QueryFrameNative.JumpBranchUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.JumpBranchUncached.native.fields ⟨0, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.JumpBranchUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.JumpBranchUncached.native.field0_0.source present0
  have sourceCell0 := congrArg (fun entries : List Source.BaseField => entries.getD 0 0) dataRow
  change Airbender.Compiler.LookupNative.JumpBranchUncached.native.field0_0.source.value (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.originalProjection) = Airbender.Compiler.MaterializedNative.JumpBranchUncached.native.model.value setupRow (.generic 0) at sourceCell0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.JumpBranchUncached.native.part0.generic_value0_0 physical data arithmetic).trans (transported0.trans sourceCell0)
  have present1 : Airbender.Compiler.LookupNative.JumpBranchUncached.native.field0_1.source ∈ Airbender.Compiler.QueryFrameNative.JumpBranchUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.JumpBranchUncached.native.fields ⟨1, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.JumpBranchUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.JumpBranchUncached.native.field0_1.source present1
  have sourceCell1 := congrArg (fun entries : List Source.BaseField => entries.getD 1 0) dataRow
  change Airbender.Compiler.LookupNative.JumpBranchUncached.native.field0_1.source.value (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.originalProjection) = Airbender.Compiler.MaterializedNative.JumpBranchUncached.native.model.value setupRow (.generic 1) at sourceCell1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.JumpBranchUncached.native.part0.generic_value0_1 physical data arithmetic).trans (transported1.trans sourceCell1)
  apply clean_pair_lookup
  rw [same0, same1]
  exact Airbender.Compiler.FixedSetupNative.JumpBranch.tag1_contains setupRow selected _

theorem generic_lookup1
    (sourceValue : Fin 55 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.JumpBranchUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.JumpBranchUncached.native.assigned (Airbender.Compiler.HelperValidityNative.JumpBranchUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.JumpBranchUncached.AuthoredLookupValid sourceValue) :
    fixedLookup1.Contains (Airbender.Compiler.CleanArithmeticNative.JumpBranchUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.JumpBranchUncached.native.genericQueries.get ⟨1, by decide⟩
  have member := authored.1 query (List.get_mem Airbender.Compiler.LookupSourceNative.JumpBranchUncached.native.genericQueries ⟨1, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  obtain ⟨setupRow, dataRow⟩ := member nonzero
  have tagProof := congrArg (fun entries : List Source.BaseField => entries.getD 9 0) dataRow
  change (5 : Source.BaseField) = Airbender.Compiler.MaterializedNative.JumpBranchUncached.native.model.value setupRow (.generic 9) at tagProof
  have selected : Airbender.Compiler.FixedSetupNative.JumpBranch.nativeSetup.value setupRow (.generic 9) = 5 := tagProof.symm
  have present0 : Airbender.Compiler.LookupNative.JumpBranchUncached.native.field1_0.source ∈ Airbender.Compiler.QueryFrameNative.JumpBranchUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.JumpBranchUncached.native.fields ⟨10, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.JumpBranchUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.JumpBranchUncached.native.field1_0.source present0
  have sourceCell0 := congrArg (fun entries : List Source.BaseField => entries.getD 0 0) dataRow
  change Airbender.Compiler.LookupNative.JumpBranchUncached.native.field1_0.source.value (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.originalProjection) = Airbender.Compiler.MaterializedNative.JumpBranchUncached.native.model.value setupRow (.generic 0) at sourceCell0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.JumpBranchUncached.native.part0.generic_value1_0 physical data arithmetic).trans (transported0.trans sourceCell0)
  have present1 : Airbender.Compiler.LookupNative.JumpBranchUncached.native.field1_1.source ∈ Airbender.Compiler.QueryFrameNative.JumpBranchUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.JumpBranchUncached.native.fields ⟨11, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.JumpBranchUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.JumpBranchUncached.native.field1_1.source present1
  have sourceCell1 := congrArg (fun entries : List Source.BaseField => entries.getD 1 0) dataRow
  change Airbender.Compiler.LookupNative.JumpBranchUncached.native.field1_1.source.value (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.originalProjection) = Airbender.Compiler.MaterializedNative.JumpBranchUncached.native.model.value setupRow (.generic 1) at sourceCell1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.JumpBranchUncached.native.part0.generic_value1_1 physical data arithmetic).trans (transported1.trans sourceCell1)
  apply clean_pair_lookup
  rw [same0, same1]
  exact Airbender.Compiler.FixedSetupNative.JumpBranch.tag5_contains setupRow selected _

theorem generic_lookup2
    (sourceValue : Fin 55 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.JumpBranchUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.JumpBranchUncached.native.assigned (Airbender.Compiler.HelperValidityNative.JumpBranchUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.JumpBranchUncached.AuthoredLookupValid sourceValue) :
    fixedLookup2.Contains (Airbender.Compiler.CleanArithmeticNative.JumpBranchUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.JumpBranchUncached.native.genericQueries.get ⟨2, by decide⟩
  have member := authored.1 query (List.get_mem Airbender.Compiler.LookupSourceNative.JumpBranchUncached.native.genericQueries ⟨2, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  obtain ⟨setupRow, dataRow⟩ := member nonzero
  have tagProof := congrArg (fun entries : List Source.BaseField => entries.getD 9 0) dataRow
  change (31 : Source.BaseField) = Airbender.Compiler.MaterializedNative.JumpBranchUncached.native.model.value setupRow (.generic 9) at tagProof
  have selected : Airbender.Compiler.FixedSetupNative.JumpBranch.nativeSetup.value setupRow (.generic 9) = 31 := tagProof.symm
  have present0 : Airbender.Compiler.LookupNative.JumpBranchUncached.native.field2_0.source ∈ Airbender.Compiler.QueryFrameNative.JumpBranchUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.JumpBranchUncached.native.fields ⟨20, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.JumpBranchUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.JumpBranchUncached.native.field2_0.source present0
  have sourceCell0 := congrArg (fun entries : List Source.BaseField => entries.getD 0 0) dataRow
  change Airbender.Compiler.LookupNative.JumpBranchUncached.native.field2_0.source.value (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.originalProjection) = Airbender.Compiler.MaterializedNative.JumpBranchUncached.native.model.value setupRow (.generic 0) at sourceCell0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.JumpBranchUncached.native.part0.generic_value2_0 physical data arithmetic).trans (transported0.trans sourceCell0)
  have present1 : Airbender.Compiler.LookupNative.JumpBranchUncached.native.field2_1.source ∈ Airbender.Compiler.QueryFrameNative.JumpBranchUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.JumpBranchUncached.native.fields ⟨21, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.JumpBranchUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.JumpBranchUncached.native.field2_1.source present1
  have sourceCell1 := congrArg (fun entries : List Source.BaseField => entries.getD 1 0) dataRow
  change Airbender.Compiler.LookupNative.JumpBranchUncached.native.field2_1.source.value (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.originalProjection) = Airbender.Compiler.MaterializedNative.JumpBranchUncached.native.model.value setupRow (.generic 1) at sourceCell1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.JumpBranchUncached.native.part0.generic_value2_1 physical data arithmetic).trans (transported1.trans sourceCell1)
  apply clean_pair_lookup
  rw [same0, same1]
  exact Airbender.Compiler.FixedSetupNative.JumpBranch.tag31_contains setupRow selected _

theorem generic_lookup3
    (sourceValue : Fin 55 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.JumpBranchUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.JumpBranchUncached.native.assigned (Airbender.Compiler.HelperValidityNative.JumpBranchUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.JumpBranchUncached.AuthoredLookupValid sourceValue) :
    fixedLookup3.Contains (Airbender.Compiler.CleanArithmeticNative.JumpBranchUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.JumpBranchUncached.native.genericQueries.get ⟨3, by decide⟩
  have member := authored.1 query (List.get_mem Airbender.Compiler.LookupSourceNative.JumpBranchUncached.native.genericQueries ⟨3, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  obtain ⟨setupRow, dataRow⟩ := member nonzero
  have tagProof := congrArg (fun entries : List Source.BaseField => entries.getD 9 0) dataRow
  change (2 : Source.BaseField) = Airbender.Compiler.MaterializedNative.JumpBranchUncached.native.model.value setupRow (.generic 9) at tagProof
  have selected : Airbender.Compiler.FixedSetupNative.JumpBranch.nativeSetup.value setupRow (.generic 9) = 2 := tagProof.symm
  have present0 : Airbender.Compiler.LookupNative.JumpBranchUncached.native.field3_0.source ∈ Airbender.Compiler.QueryFrameNative.JumpBranchUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.JumpBranchUncached.native.fields ⟨30, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.JumpBranchUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.JumpBranchUncached.native.field3_0.source present0
  have sourceCell0 := congrArg (fun entries : List Source.BaseField => entries.getD 0 0) dataRow
  change Airbender.Compiler.LookupNative.JumpBranchUncached.native.field3_0.source.value (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.originalProjection) = Airbender.Compiler.MaterializedNative.JumpBranchUncached.native.model.value setupRow (.generic 0) at sourceCell0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.JumpBranchUncached.native.part0.generic_value3_0 physical data arithmetic).trans (transported0.trans sourceCell0)
  have present1 : Airbender.Compiler.LookupNative.JumpBranchUncached.native.field3_1.source ∈ Airbender.Compiler.QueryFrameNative.JumpBranchUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.JumpBranchUncached.native.fields ⟨31, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.JumpBranchUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.JumpBranchUncached.native.field3_1.source present1
  have sourceCell1 := congrArg (fun entries : List Source.BaseField => entries.getD 1 0) dataRow
  change Airbender.Compiler.LookupNative.JumpBranchUncached.native.field3_1.source.value (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.originalProjection) = Airbender.Compiler.MaterializedNative.JumpBranchUncached.native.model.value setupRow (.generic 1) at sourceCell1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.JumpBranchUncached.native.part0.generic_value3_1 physical data arithmetic).trans (transported1.trans sourceCell1)
  have present2 : Airbender.Compiler.LookupNative.JumpBranchUncached.native.field3_2.source ∈ Airbender.Compiler.QueryFrameNative.JumpBranchUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.JumpBranchUncached.native.fields ⟨32, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.JumpBranchUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.JumpBranchUncached.native.field3_2.source present2
  have sourceCell2 := congrArg (fun entries : List Source.BaseField => entries.getD 2 0) dataRow
  change Airbender.Compiler.LookupNative.JumpBranchUncached.native.field3_2.source.value (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.originalProjection) = Airbender.Compiler.MaterializedNative.JumpBranchUncached.native.model.value setupRow (.generic 2) at sourceCell2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.JumpBranchUncached.native.part0.generic_value3_2 physical data arithmetic).trans (transported2.trans sourceCell2)
  apply clean_triple_lookup
  rw [same0, same1, same2]
  exact Airbender.Compiler.FixedSetupNative.JumpBranch.tag2_contains setupRow selected _

theorem retained_clock_from_source
    (sourceValue : Fin 55 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.JumpBranchUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.JumpBranchUncached.native.assigned (Airbender.Compiler.HelperValidityNative.JumpBranchUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.bank.address) = 0)
    (helpers : ∀ field ∈ Airbender.Compiler.HelperNative.JumpBranchUncached.native.fields, (field.value (Airbender.Compiler.HelperNative.JumpBranchUncached.native.sourceValues physical)).val < 524288)
    (authored : Airbender.Compiler.MaterializedWitnessNative.JumpBranchUncached.AuthoredLookupValid sourceValue) :
    FlatOperation.ConstraintsHoldFlat (Airbender.Compiler.CleanArithmeticNative.JumpBranchUncached.native.environment physical data) (Airbender.JumpBranchSlt.clockConstraints (p := babyBearModulus)) := by
  apply Airbender.Compiler.CleanLinksNative.JumpBranchUncached.retained_clock_constraints physical data arithmetic
  rw [clock_lookup_inventory]
  exact PredicateChecks.all (PredicateChecks.cons (range_lookup0 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (range_lookup1 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (range_lookup2 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (range_lookup3 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (generic_lookup0 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (generic_lookup1 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (generic_lookup2 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (generic_lookup3 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.JumpBranchUncached.native.timestampExpression0 (Airbender.Compiler.CleanArithmeticNative.JumpBranchUncached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.JumpBranchUncached.native.timestamp_bound0 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.JumpBranchUncached.native.timestampExpression1 (Airbender.Compiler.CleanArithmeticNative.JumpBranchUncached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.JumpBranchUncached.native.timestamp_bound1 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.JumpBranchUncached.native.timestampExpression2 (Airbender.Compiler.CleanArithmeticNative.JumpBranchUncached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.JumpBranchUncached.native.timestamp_bound2 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.JumpBranchUncached.native.timestampExpression3 (Airbender.Compiler.CleanArithmeticNative.JumpBranchUncached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.JumpBranchUncached.native.timestamp_bound3 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.JumpBranchUncached.native.timestampExpression4 (Airbender.Compiler.CleanArithmeticNative.JumpBranchUncached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.JumpBranchUncached.native.timestamp_bound4 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.JumpBranchUncached.native.timestampExpression5 (Airbender.Compiler.CleanArithmeticNative.JumpBranchUncached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.JumpBranchUncached.native.timestamp_bound5 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.JumpBranchUncached.native.timestampExpression6 (Airbender.Compiler.CleanArithmeticNative.JumpBranchUncached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.JumpBranchUncached.native.timestamp_bound6 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.JumpBranchUncached.native.timestampExpression7 (Airbender.Compiler.CleanArithmeticNative.JumpBranchUncached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.JumpBranchUncached.native.timestamp_bound7 physical data arithmetic helpers)) PredicateChecks.nil))))))))))))))))

end Airbender.Compiler.CleanClosedNative.JumpBranchUncached
