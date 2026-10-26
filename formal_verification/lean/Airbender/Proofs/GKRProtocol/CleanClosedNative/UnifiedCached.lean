import Airbender.Proofs.GKRProtocol.CleanArgumentsNative.UnifiedCached
import Airbender.Proofs.GKRProtocol.CleanScalarNative.UnifiedCached
import Airbender.Proofs.GKRProtocol.CleanPrimitiveLookups
import Airbender.Proofs.GKRProtocol.CleanLinksNative.UnifiedCached
import Airbender.Proofs.GKRProtocol.MaterializedWitnessNative.UnifiedCached
import Airbender.Proofs.GKRProtocol.CleanGenericArgumentsNative.UnifiedCached
import Airbender.Proofs.GKRProtocol.CleanGenericSetup

namespace Airbender.Compiler.CleanClosedNative.UnifiedCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

noncomputable def nativeSetup : Table Source.BaseField (fields 10) :=
  Airbender.Compiler.MaterializedNative.UnifiedCached.native.model.imported.data.table "Airbender.Native.UnifiedReduced"

theorem generic_columns_inventory : Airbender.Compiler.TableNative.UnifiedCached.native.genericSetupColumns =
    (List.range 10).map SourceSetupColumn.generic := by decide +kernel

theorem clock_lookup_inventory :
    FlatOperation.lookups (Airbender.UnifiedReduced.clockConstraints (p := babyBearModulus) nativeSetup) =
    (Airbender.Compiler.CleanArgumentsNative.UnifiedCached.native.rangeExpressions.map Verification.range16) ++
    (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.genericExpressions.map (fun entry => Lookup.mk nativeSetup.toRaw entry)) ++
    (Airbender.Compiler.CleanArgumentsNative.UnifiedCached.native.timestampExpressions.map Trace.timestampLookup) := by rfl

theorem range_lookup0
    (sourceValue : Fin 145 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.UnifiedCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.UnifiedCached.native.assigned (Airbender.Compiler.HelperValidityNative.UnifiedCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.UnifiedCached.AuthoredLookupValid sourceValue) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.UnifiedCached.native.rangeExpression0).Contains (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.UnifiedCached.native.range16Queries.get ⟨0, by decide⟩
  have member := authored.2 query (List.get_mem Airbender.Compiler.LookupSourceNative.UnifiedCached.native.range16Queries ⟨0, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.UnifiedCached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.UnifiedCached.native.field5_0.source.value (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.originalProjection)] := member nonzero
  have present : Airbender.Compiler.LookupNative.UnifiedCached.native.field5_0.source ∈ Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields ⟨61, by decide⟩
  have transported := Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.UnifiedCached.native.field5_0.source present
  have same := (Airbender.Compiler.CleanArgumentsNative.UnifiedCached.native.range_value0 physical data arithmetic).trans transported
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.UnifiedCached.native.range16_clean_refinement _ valid _

theorem range_lookup1
    (sourceValue : Fin 145 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.UnifiedCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.UnifiedCached.native.assigned (Airbender.Compiler.HelperValidityNative.UnifiedCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.UnifiedCached.AuthoredLookupValid sourceValue) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.UnifiedCached.native.rangeExpression1).Contains (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.UnifiedCached.native.range16Queries.get ⟨1, by decide⟩
  have member := authored.2 query (List.get_mem Airbender.Compiler.LookupSourceNative.UnifiedCached.native.range16Queries ⟨1, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.UnifiedCached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.UnifiedCached.native.field6_0.source.value (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.originalProjection)] := member nonzero
  have present : Airbender.Compiler.LookupNative.UnifiedCached.native.field6_0.source ∈ Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields ⟨62, by decide⟩
  have transported := Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.UnifiedCached.native.field6_0.source present
  have same := (Airbender.Compiler.CleanArgumentsNative.UnifiedCached.native.range_value1 physical data arithmetic).trans transported
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.UnifiedCached.native.range16_clean_refinement _ valid _

theorem range_lookup2
    (sourceValue : Fin 145 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.UnifiedCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.UnifiedCached.native.assigned (Airbender.Compiler.HelperValidityNative.UnifiedCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.UnifiedCached.AuthoredLookupValid sourceValue) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.UnifiedCached.native.rangeExpression2).Contains (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.UnifiedCached.native.range16Queries.get ⟨2, by decide⟩
  have member := authored.2 query (List.get_mem Airbender.Compiler.LookupSourceNative.UnifiedCached.native.range16Queries ⟨2, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.UnifiedCached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.UnifiedCached.native.field7_0.source.value (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.originalProjection)] := member nonzero
  have present : Airbender.Compiler.LookupNative.UnifiedCached.native.field7_0.source ∈ Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields ⟨63, by decide⟩
  have transported := Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.UnifiedCached.native.field7_0.source present
  have same := (Airbender.Compiler.CleanArgumentsNative.UnifiedCached.native.range_value2 physical data arithmetic).trans transported
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.UnifiedCached.native.range16_clean_refinement _ valid _

theorem range_lookup3
    (sourceValue : Fin 145 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.UnifiedCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.UnifiedCached.native.assigned (Airbender.Compiler.HelperValidityNative.UnifiedCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.UnifiedCached.AuthoredLookupValid sourceValue) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.UnifiedCached.native.rangeExpression3).Contains (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.UnifiedCached.native.range16Queries.get ⟨3, by decide⟩
  have member := authored.2 query (List.get_mem Airbender.Compiler.LookupSourceNative.UnifiedCached.native.range16Queries ⟨3, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.UnifiedCached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.UnifiedCached.native.field8_0.source.value (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.originalProjection)] := member nonzero
  have present : Airbender.Compiler.LookupNative.UnifiedCached.native.field8_0.source ∈ Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields ⟨64, by decide⟩
  have transported := Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.UnifiedCached.native.field8_0.source present
  have same := (Airbender.Compiler.CleanArgumentsNative.UnifiedCached.native.range_value3 physical data arithmetic).trans transported
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.UnifiedCached.native.range16_clean_refinement _ valid _

theorem range_lookup4
    (sourceValue : Fin 145 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.UnifiedCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.UnifiedCached.native.assigned (Airbender.Compiler.HelperValidityNative.UnifiedCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.UnifiedCached.AuthoredLookupValid sourceValue) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.UnifiedCached.native.rangeExpression4).Contains (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.UnifiedCached.native.range16Queries.get ⟨4, by decide⟩
  have member := authored.2 query (List.get_mem Airbender.Compiler.LookupSourceNative.UnifiedCached.native.range16Queries ⟨4, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.UnifiedCached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.UnifiedCached.native.field9_0.source.value (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.originalProjection)] := member nonzero
  have present : Airbender.Compiler.LookupNative.UnifiedCached.native.field9_0.source ∈ Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields ⟨65, by decide⟩
  have transported := Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.UnifiedCached.native.field9_0.source present
  have same := (Airbender.Compiler.CleanArgumentsNative.UnifiedCached.native.range_value4 physical data arithmetic).trans transported
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.UnifiedCached.native.range16_clean_refinement _ valid _

theorem range_lookup5
    (sourceValue : Fin 145 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.UnifiedCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.UnifiedCached.native.assigned (Airbender.Compiler.HelperValidityNative.UnifiedCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.UnifiedCached.AuthoredLookupValid sourceValue) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.UnifiedCached.native.rangeExpression5).Contains (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.UnifiedCached.native.range16Queries.get ⟨5, by decide⟩
  have member := authored.2 query (List.get_mem Airbender.Compiler.LookupSourceNative.UnifiedCached.native.range16Queries ⟨5, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.UnifiedCached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.UnifiedCached.native.field10_0.source.value (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.originalProjection)] := member nonzero
  have present : Airbender.Compiler.LookupNative.UnifiedCached.native.field10_0.source ∈ Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields ⟨66, by decide⟩
  have transported := Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.UnifiedCached.native.field10_0.source present
  have same := (Airbender.Compiler.CleanArgumentsNative.UnifiedCached.native.range_value5 physical data arithmetic).trans transported
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.UnifiedCached.native.range16_clean_refinement _ valid _

theorem range_lookup6
    (sourceValue : Fin 145 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.UnifiedCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.UnifiedCached.native.assigned (Airbender.Compiler.HelperValidityNative.UnifiedCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.UnifiedCached.AuthoredLookupValid sourceValue) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.UnifiedCached.native.rangeExpression6).Contains (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.UnifiedCached.native.range16Queries.get ⟨6, by decide⟩
  have member := authored.2 query (List.get_mem Airbender.Compiler.LookupSourceNative.UnifiedCached.native.range16Queries ⟨6, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.UnifiedCached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.UnifiedCached.native.field11_0.source.value (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.originalProjection)] := member nonzero
  have present : Airbender.Compiler.LookupNative.UnifiedCached.native.field11_0.source ∈ Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields ⟨67, by decide⟩
  have transported := Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.UnifiedCached.native.field11_0.source present
  have same := (Airbender.Compiler.CleanArgumentsNative.UnifiedCached.native.range_value6 physical data arithmetic).trans transported
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.UnifiedCached.native.range16_clean_refinement _ valid _

theorem range_lookup7
    (sourceValue : Fin 145 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.UnifiedCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.UnifiedCached.native.assigned (Airbender.Compiler.HelperValidityNative.UnifiedCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.UnifiedCached.AuthoredLookupValid sourceValue) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.UnifiedCached.native.rangeExpression7).Contains (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.UnifiedCached.native.range16Queries.get ⟨7, by decide⟩
  have member := authored.2 query (List.get_mem Airbender.Compiler.LookupSourceNative.UnifiedCached.native.range16Queries ⟨7, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.UnifiedCached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.UnifiedCached.native.field12_0.source.value (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.originalProjection)] := member nonzero
  have present : Airbender.Compiler.LookupNative.UnifiedCached.native.field12_0.source ∈ Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields ⟨68, by decide⟩
  have transported := Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.UnifiedCached.native.field12_0.source present
  have same := (Airbender.Compiler.CleanArgumentsNative.UnifiedCached.native.range_value7 physical data arithmetic).trans transported
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.UnifiedCached.native.range16_clean_refinement _ valid _

theorem range_lookup8
    (sourceValue : Fin 145 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.UnifiedCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.UnifiedCached.native.assigned (Airbender.Compiler.HelperValidityNative.UnifiedCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.UnifiedCached.AuthoredLookupValid sourceValue) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.UnifiedCached.native.rangeExpression8).Contains (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.UnifiedCached.native.range16Queries.get ⟨8, by decide⟩
  have member := authored.2 query (List.get_mem Airbender.Compiler.LookupSourceNative.UnifiedCached.native.range16Queries ⟨8, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.UnifiedCached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.UnifiedCached.native.field13_0.source.value (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.originalProjection)] := member nonzero
  have present : Airbender.Compiler.LookupNative.UnifiedCached.native.field13_0.source ∈ Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields ⟨69, by decide⟩
  have transported := Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.UnifiedCached.native.field13_0.source present
  have same := (Airbender.Compiler.CleanArgumentsNative.UnifiedCached.native.range_value8 physical data arithmetic).trans transported
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.UnifiedCached.native.range16_clean_refinement _ valid _

theorem range_lookup9
    (sourceValue : Fin 145 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.UnifiedCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.UnifiedCached.native.assigned (Airbender.Compiler.HelperValidityNative.UnifiedCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.UnifiedCached.AuthoredLookupValid sourceValue) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.UnifiedCached.native.rangeExpression9).Contains (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.UnifiedCached.native.range16Queries.get ⟨9, by decide⟩
  have member := authored.2 query (List.get_mem Airbender.Compiler.LookupSourceNative.UnifiedCached.native.range16Queries ⟨9, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.UnifiedCached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.UnifiedCached.native.field14_0.source.value (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.originalProjection)] := member nonzero
  have present : Airbender.Compiler.LookupNative.UnifiedCached.native.field14_0.source ∈ Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields ⟨70, by decide⟩
  have transported := Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.UnifiedCached.native.field14_0.source present
  have same := (Airbender.Compiler.CleanArgumentsNative.UnifiedCached.native.range_value9 physical data arithmetic).trans transported
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.UnifiedCached.native.range16_clean_refinement _ valid _

theorem range_lookup10
    (sourceValue : Fin 145 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.UnifiedCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.UnifiedCached.native.assigned (Airbender.Compiler.HelperValidityNative.UnifiedCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.UnifiedCached.AuthoredLookupValid sourceValue) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.UnifiedCached.native.rangeExpression10).Contains (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.UnifiedCached.native.range16Queries.get ⟨10, by decide⟩
  have member := authored.2 query (List.get_mem Airbender.Compiler.LookupSourceNative.UnifiedCached.native.range16Queries ⟨10, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.UnifiedCached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.UnifiedCached.native.field15_0.source.value (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.originalProjection)] := member nonzero
  have present : Airbender.Compiler.LookupNative.UnifiedCached.native.field15_0.source ∈ Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields ⟨71, by decide⟩
  have transported := Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.UnifiedCached.native.field15_0.source present
  have same := (Airbender.Compiler.CleanArgumentsNative.UnifiedCached.native.range_value10 physical data arithmetic).trans transported
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.UnifiedCached.native.range16_clean_refinement _ valid _

theorem range_lookup11
    (sourceValue : Fin 145 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.UnifiedCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.UnifiedCached.native.assigned (Airbender.Compiler.HelperValidityNative.UnifiedCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.UnifiedCached.AuthoredLookupValid sourceValue) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.UnifiedCached.native.rangeExpression11).Contains (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.UnifiedCached.native.range16Queries.get ⟨11, by decide⟩
  have member := authored.2 query (List.get_mem Airbender.Compiler.LookupSourceNative.UnifiedCached.native.range16Queries ⟨11, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.UnifiedCached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.UnifiedCached.native.field16_0.source.value (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.originalProjection)] := member nonzero
  have present : Airbender.Compiler.LookupNative.UnifiedCached.native.field16_0.source ∈ Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields ⟨72, by decide⟩
  have transported := Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.UnifiedCached.native.field16_0.source present
  have same := (Airbender.Compiler.CleanArgumentsNative.UnifiedCached.native.range_value11 physical data arithmetic).trans transported
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.UnifiedCached.native.range16_clean_refinement _ valid _

theorem range_lookup12
    (sourceValue : Fin 145 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.UnifiedCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.UnifiedCached.native.assigned (Airbender.Compiler.HelperValidityNative.UnifiedCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.UnifiedCached.AuthoredLookupValid sourceValue) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.UnifiedCached.native.rangeExpression12).Contains (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.UnifiedCached.native.range16Queries.get ⟨12, by decide⟩
  have member := authored.2 query (List.get_mem Airbender.Compiler.LookupSourceNative.UnifiedCached.native.range16Queries ⟨12, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.UnifiedCached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.UnifiedCached.native.field17_0.source.value (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.originalProjection)] := member nonzero
  have present : Airbender.Compiler.LookupNative.UnifiedCached.native.field17_0.source ∈ Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields ⟨73, by decide⟩
  have transported := Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.UnifiedCached.native.field17_0.source present
  have same := (Airbender.Compiler.CleanArgumentsNative.UnifiedCached.native.range_value12 physical data arithmetic).trans transported
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.UnifiedCached.native.range16_clean_refinement _ valid _

theorem generic_lookup0
    (sourceValue : Fin 145 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.UnifiedCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.UnifiedCached.native.assigned (Airbender.Compiler.HelperValidityNative.UnifiedCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.UnifiedCached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.genericExpressions0).Contains (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.UnifiedCached.native.genericQueries.get ⟨0, by decide⟩
  have member := authored.1 query (List.get_mem Airbender.Compiler.LookupSourceNative.UnifiedCached.native.genericQueries ⟨0, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.UnifiedCached.native.field0_0.source ∈ Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields ⟨0, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.UnifiedCached.native.field0_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.generic_value0_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.UnifiedCached.native.field0_1.source ∈ Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields ⟨1, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.UnifiedCached.native.field0_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.generic_value0_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.UnifiedCached.native.field0_2.source ∈ Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields ⟨2, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.UnifiedCached.native.field0_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.generic_value0_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.UnifiedCached.native.field0_3.source ∈ Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields ⟨3, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.UnifiedCached.native.field0_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.generic_value0_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.UnifiedCached.native.field0_4.source ∈ Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields ⟨4, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.UnifiedCached.native.field0_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.generic_value0_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.UnifiedCached.native.field0_5.source ∈ Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields ⟨5, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.UnifiedCached.native.field0_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.generic_value0_5 physical data arithmetic).trans transported5
  have present6 : Airbender.Compiler.LookupNative.UnifiedCached.native.field0_6.source ∈ Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields ⟨6, by decide⟩
  have transported6 := Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.UnifiedCached.native.field0_6.source present6
  have same6 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.generic_value0_6 physical data arithmetic).trans transported6
  have present7 : Airbender.Compiler.LookupNative.UnifiedCached.native.field0_7.source ∈ Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields ⟨7, by decide⟩
  have transported7 := Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.UnifiedCached.native.field0_7.source present7
  have same7 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.generic_value0_7 physical data arithmetic).trans transported7
  have present8 : Airbender.Compiler.LookupNative.UnifiedCached.native.field0_8.source ∈ Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields ⟨8, by decide⟩
  have transported8 := Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.UnifiedCached.native.field0_8.source present8
  have same8 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.generic_value0_8 physical data arithmetic).trans transported8
  have present9 : Airbender.Compiler.LookupNative.UnifiedCached.native.field0_9.source ∈ Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields ⟨9, by decide⟩
  have transported9 := Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.UnifiedCached.native.field0_9.source present9
  have same9 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.generic_value0_9 physical data arithmetic).trans transported9
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.UnifiedCached.native.model.generic_clean_contains Airbender.Compiler.TableNative.UnifiedCached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.UnifiedReduced" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.genericExpressions0, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.UnifiedCached.native.model.Contains Airbender.Compiler.TableNative.UnifiedCached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.genericExpression0_0.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.genericExpression0_1.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.genericExpression0_2.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.genericExpression0_3.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.genericExpression0_4.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.genericExpression0_5.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.genericExpression0_6.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.genericExpression0_7.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.genericExpression0_8.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.genericExpression0_9.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5, same6, same7, same8, same9]
  exact valid

theorem generic_lookup1
    (sourceValue : Fin 145 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.UnifiedCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.UnifiedCached.native.assigned (Airbender.Compiler.HelperValidityNative.UnifiedCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.UnifiedCached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.genericExpressions1).Contains (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.UnifiedCached.native.genericQueries.get ⟨1, by decide⟩
  have member := authored.1 query (List.get_mem Airbender.Compiler.LookupSourceNative.UnifiedCached.native.genericQueries ⟨1, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.UnifiedCached.native.field1_0.source ∈ Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields ⟨10, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.UnifiedCached.native.field1_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.generic_value1_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.UnifiedCached.native.field1_1.source ∈ Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields ⟨11, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.UnifiedCached.native.field1_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.generic_value1_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.UnifiedCached.native.field1_2.source ∈ Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields ⟨12, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.UnifiedCached.native.field1_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.generic_value1_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.UnifiedCached.native.field1_3.source ∈ Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields ⟨13, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.UnifiedCached.native.field1_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.generic_value1_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.UnifiedCached.native.field1_4.source ∈ Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields ⟨14, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.UnifiedCached.native.field1_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.generic_value1_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.UnifiedCached.native.field1_5.source ∈ Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields ⟨15, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.UnifiedCached.native.field1_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.generic_value1_5 physical data arithmetic).trans transported5
  have present6 : Airbender.Compiler.LookupNative.UnifiedCached.native.field1_6.source ∈ Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields ⟨16, by decide⟩
  have transported6 := Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.UnifiedCached.native.field1_6.source present6
  have same6 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.generic_value1_6 physical data arithmetic).trans transported6
  have present7 : Airbender.Compiler.LookupNative.UnifiedCached.native.field1_7.source ∈ Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields ⟨17, by decide⟩
  have transported7 := Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.UnifiedCached.native.field1_7.source present7
  have same7 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.generic_value1_7 physical data arithmetic).trans transported7
  have present8 : Airbender.Compiler.LookupNative.UnifiedCached.native.field1_8.source ∈ Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields ⟨18, by decide⟩
  have transported8 := Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.UnifiedCached.native.field1_8.source present8
  have same8 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.generic_value1_8 physical data arithmetic).trans transported8
  have present9 : Airbender.Compiler.LookupNative.UnifiedCached.native.field1_9.source ∈ Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields ⟨19, by decide⟩
  have transported9 := Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.UnifiedCached.native.field1_9.source present9
  have same9 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.generic_value1_9 physical data arithmetic).trans transported9
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.UnifiedCached.native.model.generic_clean_contains Airbender.Compiler.TableNative.UnifiedCached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.UnifiedReduced" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.genericExpressions1, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.UnifiedCached.native.model.Contains Airbender.Compiler.TableNative.UnifiedCached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.genericExpression1_0.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.genericExpression1_1.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.genericExpression1_2.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.genericExpression1_3.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.genericExpression1_4.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.genericExpression1_5.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.genericExpression1_6.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.genericExpression1_7.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.genericExpression1_8.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.genericExpression1_9.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5, same6, same7, same8, same9]
  exact valid

theorem generic_lookup2
    (sourceValue : Fin 145 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.UnifiedCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.UnifiedCached.native.assigned (Airbender.Compiler.HelperValidityNative.UnifiedCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.UnifiedCached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.genericExpressions2).Contains (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.UnifiedCached.native.genericQueries.get ⟨2, by decide⟩
  have member := authored.1 query (List.get_mem Airbender.Compiler.LookupSourceNative.UnifiedCached.native.genericQueries ⟨2, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.UnifiedCached.native.field2_0.source ∈ Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields ⟨20, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.UnifiedCached.native.field2_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.generic_value2_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.UnifiedCached.native.field2_1.source ∈ Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields ⟨21, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.UnifiedCached.native.field2_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.generic_value2_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.UnifiedCached.native.field2_2.source ∈ Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields ⟨22, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.UnifiedCached.native.field2_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.generic_value2_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.UnifiedCached.native.field2_3.source ∈ Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields ⟨23, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.UnifiedCached.native.field2_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.generic_value2_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.UnifiedCached.native.field2_4.source ∈ Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields ⟨24, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.UnifiedCached.native.field2_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.generic_value2_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.UnifiedCached.native.field2_5.source ∈ Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields ⟨25, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.UnifiedCached.native.field2_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.generic_value2_5 physical data arithmetic).trans transported5
  have present6 : Airbender.Compiler.LookupNative.UnifiedCached.native.field2_6.source ∈ Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields ⟨26, by decide⟩
  have transported6 := Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.UnifiedCached.native.field2_6.source present6
  have same6 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.generic_value2_6 physical data arithmetic).trans transported6
  have present7 : Airbender.Compiler.LookupNative.UnifiedCached.native.field2_7.source ∈ Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields ⟨27, by decide⟩
  have transported7 := Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.UnifiedCached.native.field2_7.source present7
  have same7 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.generic_value2_7 physical data arithmetic).trans transported7
  have present8 : Airbender.Compiler.LookupNative.UnifiedCached.native.field2_8.source ∈ Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields ⟨28, by decide⟩
  have transported8 := Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.UnifiedCached.native.field2_8.source present8
  have same8 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.generic_value2_8 physical data arithmetic).trans transported8
  have present9 : Airbender.Compiler.LookupNative.UnifiedCached.native.field2_9.source ∈ Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields ⟨29, by decide⟩
  have transported9 := Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.UnifiedCached.native.field2_9.source present9
  have same9 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.generic_value2_9 physical data arithmetic).trans transported9
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.UnifiedCached.native.model.generic_clean_contains Airbender.Compiler.TableNative.UnifiedCached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.UnifiedReduced" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.genericExpressions2, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.UnifiedCached.native.model.Contains Airbender.Compiler.TableNative.UnifiedCached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.genericExpression2_0.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.genericExpression2_1.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.genericExpression2_2.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.genericExpression2_3.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.genericExpression2_4.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.genericExpression2_5.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.genericExpression2_6.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.genericExpression2_7.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.genericExpression2_8.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.genericExpression2_9.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5, same6, same7, same8, same9]
  exact valid

theorem generic_lookup3
    (sourceValue : Fin 145 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.UnifiedCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.UnifiedCached.native.assigned (Airbender.Compiler.HelperValidityNative.UnifiedCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.UnifiedCached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.genericExpressions3).Contains (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.UnifiedCached.native.genericQueries.get ⟨3, by decide⟩
  have member := authored.1 query (List.get_mem Airbender.Compiler.LookupSourceNative.UnifiedCached.native.genericQueries ⟨3, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.UnifiedCached.native.field3_0.source ∈ Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields ⟨30, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.UnifiedCached.native.field3_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.generic_value3_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.UnifiedCached.native.field3_1.source ∈ Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields ⟨31, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.UnifiedCached.native.field3_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.generic_value3_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.UnifiedCached.native.field3_2.source ∈ Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields ⟨32, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.UnifiedCached.native.field3_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.generic_value3_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.UnifiedCached.native.field3_3.source ∈ Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields ⟨33, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.UnifiedCached.native.field3_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.generic_value3_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.UnifiedCached.native.field3_4.source ∈ Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields ⟨34, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.UnifiedCached.native.field3_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.generic_value3_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.UnifiedCached.native.field3_5.source ∈ Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields ⟨35, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.UnifiedCached.native.field3_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.generic_value3_5 physical data arithmetic).trans transported5
  have present6 : Airbender.Compiler.LookupNative.UnifiedCached.native.field3_6.source ∈ Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields ⟨36, by decide⟩
  have transported6 := Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.UnifiedCached.native.field3_6.source present6
  have same6 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.generic_value3_6 physical data arithmetic).trans transported6
  have present7 : Airbender.Compiler.LookupNative.UnifiedCached.native.field3_7.source ∈ Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields ⟨37, by decide⟩
  have transported7 := Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.UnifiedCached.native.field3_7.source present7
  have same7 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.generic_value3_7 physical data arithmetic).trans transported7
  have present8 : Airbender.Compiler.LookupNative.UnifiedCached.native.field3_8.source ∈ Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields ⟨38, by decide⟩
  have transported8 := Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.UnifiedCached.native.field3_8.source present8
  have same8 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.generic_value3_8 physical data arithmetic).trans transported8
  have present9 : Airbender.Compiler.LookupNative.UnifiedCached.native.field3_9.source ∈ Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields ⟨39, by decide⟩
  have transported9 := Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.UnifiedCached.native.field3_9.source present9
  have same9 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.generic_value3_9 physical data arithmetic).trans transported9
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.UnifiedCached.native.model.generic_clean_contains Airbender.Compiler.TableNative.UnifiedCached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.UnifiedReduced" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.genericExpressions3, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.UnifiedCached.native.model.Contains Airbender.Compiler.TableNative.UnifiedCached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.genericExpression3_0.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.genericExpression3_1.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.genericExpression3_2.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.genericExpression3_3.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.genericExpression3_4.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.genericExpression3_5.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.genericExpression3_6.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.genericExpression3_7.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.genericExpression3_8.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.genericExpression3_9.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5, same6, same7, same8, same9]
  exact valid

theorem generic_lookup4
    (sourceValue : Fin 145 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.UnifiedCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.UnifiedCached.native.assigned (Airbender.Compiler.HelperValidityNative.UnifiedCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.UnifiedCached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.genericExpressions4).Contains (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.UnifiedCached.native.genericQueries.get ⟨4, by decide⟩
  have member := authored.1 query (List.get_mem Airbender.Compiler.LookupSourceNative.UnifiedCached.native.genericQueries ⟨4, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.UnifiedCached.native.field4_0.source ∈ Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields ⟨40, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.UnifiedCached.native.field4_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.generic_value4_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.UnifiedCached.native.field4_1.source ∈ Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields ⟨41, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.UnifiedCached.native.field4_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.generic_value4_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.UnifiedCached.native.field4_2.source ∈ Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields ⟨42, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.UnifiedCached.native.field4_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.generic_value4_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.UnifiedCached.native.field4_3.source ∈ Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields ⟨43, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.UnifiedCached.native.field4_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.generic_value4_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.UnifiedCached.native.field4_4.source ∈ Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields ⟨44, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.UnifiedCached.native.field4_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.generic_value4_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.UnifiedCached.native.field4_5.source ∈ Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields ⟨45, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.UnifiedCached.native.field4_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.generic_value4_5 physical data arithmetic).trans transported5
  have present6 : Airbender.Compiler.LookupNative.UnifiedCached.native.field4_6.source ∈ Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields ⟨46, by decide⟩
  have transported6 := Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.UnifiedCached.native.field4_6.source present6
  have same6 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.generic_value4_6 physical data arithmetic).trans transported6
  have present7 : Airbender.Compiler.LookupNative.UnifiedCached.native.field4_7.source ∈ Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields ⟨47, by decide⟩
  have transported7 := Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.UnifiedCached.native.field4_7.source present7
  have same7 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.generic_value4_7 physical data arithmetic).trans transported7
  have present8 : Airbender.Compiler.LookupNative.UnifiedCached.native.field4_8.source ∈ Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields ⟨48, by decide⟩
  have transported8 := Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.UnifiedCached.native.field4_8.source present8
  have same8 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.generic_value4_8 physical data arithmetic).trans transported8
  have present9 : Airbender.Compiler.LookupNative.UnifiedCached.native.field4_9.source ∈ Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields ⟨49, by decide⟩
  have transported9 := Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.UnifiedCached.native.field4_9.source present9
  have same9 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.generic_value4_9 physical data arithmetic).trans transported9
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.UnifiedCached.native.model.generic_clean_contains Airbender.Compiler.TableNative.UnifiedCached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.UnifiedReduced" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.genericExpressions4, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.UnifiedCached.native.model.Contains Airbender.Compiler.TableNative.UnifiedCached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.genericExpression4_0.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.genericExpression4_1.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.genericExpression4_2.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.genericExpression4_3.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.genericExpression4_4.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.genericExpression4_5.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.genericExpression4_6.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.genericExpression4_7.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.genericExpression4_8.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.genericExpression4_9.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5, same6, same7, same8, same9]
  exact valid

theorem retained_clock_from_source
    (sourceValue : Fin 145 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.UnifiedCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.UnifiedCached.native.assigned (Airbender.Compiler.HelperValidityNative.UnifiedCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0)
    (helpers : ∀ field ∈ Airbender.Compiler.HelperNative.UnifiedCached.native.fields, (field.value (Airbender.Compiler.HelperNative.UnifiedCached.native.sourceValues physical)).val < 524288)
    (authored : Airbender.Compiler.MaterializedWitnessNative.UnifiedCached.AuthoredLookupValid sourceValue) :
    FlatOperation.ConstraintsHoldFlat (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data) (Airbender.UnifiedReduced.clockConstraints (p := babyBearModulus) nativeSetup) := by
  apply Airbender.Compiler.CleanLinksNative.UnifiedCached.retained_clock_constraints nativeSetup physical data arithmetic
  rw [clock_lookup_inventory]
  exact PredicateChecks.all (PredicateChecks.cons (range_lookup0 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (range_lookup1 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (range_lookup2 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (range_lookup3 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (range_lookup4 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (range_lookup5 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (range_lookup6 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (range_lookup7 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (range_lookup8 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (range_lookup9 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (range_lookup10 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (range_lookup11 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (range_lookup12 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (generic_lookup0 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (generic_lookup1 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (generic_lookup2 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (generic_lookup3 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (generic_lookup4 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.UnifiedCached.native.timestampExpression0 (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.UnifiedCached.native.timestamp_bound0 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.UnifiedCached.native.timestampExpression1 (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.UnifiedCached.native.timestamp_bound1 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.UnifiedCached.native.timestampExpression2 (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.UnifiedCached.native.timestamp_bound2 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.UnifiedCached.native.timestampExpression3 (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.UnifiedCached.native.timestamp_bound3 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.UnifiedCached.native.timestampExpression4 (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.UnifiedCached.native.timestamp_bound4 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.UnifiedCached.native.timestampExpression5 (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.UnifiedCached.native.timestamp_bound5 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.UnifiedCached.native.timestampExpression6 (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.UnifiedCached.native.timestamp_bound6 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.UnifiedCached.native.timestampExpression7 (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.UnifiedCached.native.timestamp_bound7 physical data arithmetic helpers)) PredicateChecks.nil))))))))))))))))))))))))))

end Airbender.Compiler.CleanClosedNative.UnifiedCached
