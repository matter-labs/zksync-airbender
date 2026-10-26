import Airbender.Proofs.GKRProtocol.CleanArgumentsNative.MulDivCached
import Airbender.Proofs.GKRProtocol.CleanScalarNative.MulDivCached
import Airbender.Proofs.GKRProtocol.CleanGenericArgumentsNative.MulDivCached
import Airbender.Proofs.GKRProtocol.FixedPrimitives
import Airbender.Proofs.GKRProtocol.FixedSetupNative.MulDivMembership
import Airbender.Proofs.GKRProtocol.CleanLinksNative.MulDivCached
import Airbender.Proofs.GKRProtocol.MaterializedWitnessNative.MulDivCached
import Airbender.Proofs.Constraints

namespace Airbender.Compiler.CleanClosedNative.MulDivCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

noncomputable def fixedLookup0 : Lookup Source.BaseField :=
  Verification.pairLookup Verification.regIsZeroTable Airbender.Compiler.CleanGenericArgumentsNative.MulDivCached.native.part0.genericExpression0_0 Airbender.Compiler.CleanGenericArgumentsNative.MulDivCached.native.part0.genericExpression0_1

noncomputable def fixedLookup1 : Lookup Source.BaseField :=
  Verification.pairLookup Verification.u16LowByteTable Airbender.Compiler.CleanGenericArgumentsNative.MulDivCached.native.part0.genericExpression1_0 Airbender.Compiler.CleanGenericArgumentsNative.MulDivCached.native.part0.genericExpression1_1

noncomputable def fixedLookup2 : Lookup Source.BaseField :=
  Verification.pairLookup Verification.u16LowByteTable Airbender.Compiler.CleanGenericArgumentsNative.MulDivCached.native.part0.genericExpression2_0 Airbender.Compiler.CleanGenericArgumentsNative.MulDivCached.native.part0.genericExpression2_1

noncomputable def fixedLookup3 : Lookup Source.BaseField :=
  Verification.range13 Airbender.Compiler.CleanGenericArgumentsNative.MulDivCached.native.part0.genericExpression3_0

noncomputable def fixedLookup4 : Lookup Source.BaseField :=
  Verification.range13 Airbender.Compiler.CleanGenericArgumentsNative.MulDivCached.native.part0.genericExpression4_0

noncomputable def fixedLookup5 : Lookup Source.BaseField :=
  Verification.range13 Airbender.Compiler.CleanGenericArgumentsNative.MulDivCached.native.part0.genericExpression5_0

noncomputable def fixedLookup6 : Lookup Source.BaseField :=
  Verification.pairLookup Verification.u16LowByteTable Airbender.Compiler.CleanGenericArgumentsNative.MulDivCached.native.part0.genericExpression6_0 Airbender.Compiler.CleanGenericArgumentsNative.MulDivCached.native.part0.genericExpression6_1

noncomputable def fixedLookup7 : Lookup Source.BaseField :=
  Verification.pairLookup Verification.u16LowByteTable Airbender.Compiler.CleanGenericArgumentsNative.MulDivCached.native.part0.genericExpression7_0 Airbender.Compiler.CleanGenericArgumentsNative.MulDivCached.native.part0.genericExpression7_1

noncomputable def fixedLookups : List (Lookup Source.BaseField) := [fixedLookup0, fixedLookup1, fixedLookup2, fixedLookup3, fixedLookup4, fixedLookup5, fixedLookup6, fixedLookup7]

theorem clock_lookup_inventory :
    FlatOperation.lookups (Airbender.MulDiv.clockConstraints (p := babyBearModulus)) =
    (Airbender.Compiler.CleanArgumentsNative.MulDivCached.native.rangeExpressions.map Verification.range16) ++ fixedLookups ++
      (Airbender.Compiler.CleanArgumentsNative.MulDivCached.native.timestampExpressions.map Trace.timestampLookup) := by rfl

theorem range_lookup0
    (sourceValue : Fin 71 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.MulDivCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.MulDivCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.MulDivCached.native.assigned (Airbender.Compiler.HelperValidityNative.MulDivCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.MulDivCached.AuthoredLookupValid sourceValue) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.MulDivCached.native.rangeExpression0).Contains (Airbender.Compiler.CleanArithmeticNative.MulDivCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.MulDivCached.native.range16Queries.get ⟨0, by decide⟩
  have member := authored.2 query (List.get_mem Airbender.Compiler.LookupSourceNative.MulDivCached.native.range16Queries ⟨0, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.MulDivCached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.MulDivCached.native.field8_0.source.value (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.originalProjection)] := member nonzero
  have present : Airbender.Compiler.LookupNative.MulDivCached.native.field8_0.source ∈ Airbender.Compiler.QueryFrameNative.MulDivCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.MulDivCached.native.fields ⟨82, by decide⟩
  have transported := Airbender.Compiler.QueryFrameNative.MulDivCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.MulDivCached.native.field8_0.source present
  have same := (Airbender.Compiler.CleanArgumentsNative.MulDivCached.native.range_value0 physical data arithmetic).trans transported
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.MulDivCached.native.range16_clean_refinement _ valid _

theorem range_lookup1
    (sourceValue : Fin 71 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.MulDivCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.MulDivCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.MulDivCached.native.assigned (Airbender.Compiler.HelperValidityNative.MulDivCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.MulDivCached.AuthoredLookupValid sourceValue) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.MulDivCached.native.rangeExpression1).Contains (Airbender.Compiler.CleanArithmeticNative.MulDivCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.MulDivCached.native.range16Queries.get ⟨1, by decide⟩
  have member := authored.2 query (List.get_mem Airbender.Compiler.LookupSourceNative.MulDivCached.native.range16Queries ⟨1, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.MulDivCached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.MulDivCached.native.field9_0.source.value (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.originalProjection)] := member nonzero
  have present : Airbender.Compiler.LookupNative.MulDivCached.native.field9_0.source ∈ Airbender.Compiler.QueryFrameNative.MulDivCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.MulDivCached.native.fields ⟨83, by decide⟩
  have transported := Airbender.Compiler.QueryFrameNative.MulDivCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.MulDivCached.native.field9_0.source present
  have same := (Airbender.Compiler.CleanArgumentsNative.MulDivCached.native.range_value1 physical data arithmetic).trans transported
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.MulDivCached.native.range16_clean_refinement _ valid _

theorem range_lookup2
    (sourceValue : Fin 71 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.MulDivCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.MulDivCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.MulDivCached.native.assigned (Airbender.Compiler.HelperValidityNative.MulDivCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.MulDivCached.AuthoredLookupValid sourceValue) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.MulDivCached.native.rangeExpression2).Contains (Airbender.Compiler.CleanArithmeticNative.MulDivCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.MulDivCached.native.range16Queries.get ⟨2, by decide⟩
  have member := authored.2 query (List.get_mem Airbender.Compiler.LookupSourceNative.MulDivCached.native.range16Queries ⟨2, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.MulDivCached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.MulDivCached.native.field10_0.source.value (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.originalProjection)] := member nonzero
  have present : Airbender.Compiler.LookupNative.MulDivCached.native.field10_0.source ∈ Airbender.Compiler.QueryFrameNative.MulDivCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.MulDivCached.native.fields ⟨84, by decide⟩
  have transported := Airbender.Compiler.QueryFrameNative.MulDivCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.MulDivCached.native.field10_0.source present
  have same := (Airbender.Compiler.CleanArgumentsNative.MulDivCached.native.range_value2 physical data arithmetic).trans transported
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.MulDivCached.native.range16_clean_refinement _ valid _

theorem range_lookup3
    (sourceValue : Fin 71 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.MulDivCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.MulDivCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.MulDivCached.native.assigned (Airbender.Compiler.HelperValidityNative.MulDivCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.MulDivCached.AuthoredLookupValid sourceValue) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.MulDivCached.native.rangeExpression3).Contains (Airbender.Compiler.CleanArithmeticNative.MulDivCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.MulDivCached.native.range16Queries.get ⟨3, by decide⟩
  have member := authored.2 query (List.get_mem Airbender.Compiler.LookupSourceNative.MulDivCached.native.range16Queries ⟨3, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.MulDivCached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.MulDivCached.native.field11_0.source.value (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.originalProjection)] := member nonzero
  have present : Airbender.Compiler.LookupNative.MulDivCached.native.field11_0.source ∈ Airbender.Compiler.QueryFrameNative.MulDivCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.MulDivCached.native.fields ⟨85, by decide⟩
  have transported := Airbender.Compiler.QueryFrameNative.MulDivCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.MulDivCached.native.field11_0.source present
  have same := (Airbender.Compiler.CleanArgumentsNative.MulDivCached.native.range_value3 physical data arithmetic).trans transported
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.MulDivCached.native.range16_clean_refinement _ valid _

theorem range_lookup4
    (sourceValue : Fin 71 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.MulDivCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.MulDivCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.MulDivCached.native.assigned (Airbender.Compiler.HelperValidityNative.MulDivCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.MulDivCached.AuthoredLookupValid sourceValue) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.MulDivCached.native.rangeExpression4).Contains (Airbender.Compiler.CleanArithmeticNative.MulDivCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.MulDivCached.native.range16Queries.get ⟨4, by decide⟩
  have member := authored.2 query (List.get_mem Airbender.Compiler.LookupSourceNative.MulDivCached.native.range16Queries ⟨4, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.MulDivCached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.MulDivCached.native.field12_0.source.value (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.originalProjection)] := member nonzero
  have present : Airbender.Compiler.LookupNative.MulDivCached.native.field12_0.source ∈ Airbender.Compiler.QueryFrameNative.MulDivCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.MulDivCached.native.fields ⟨86, by decide⟩
  have transported := Airbender.Compiler.QueryFrameNative.MulDivCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.MulDivCached.native.field12_0.source present
  have same := (Airbender.Compiler.CleanArgumentsNative.MulDivCached.native.range_value4 physical data arithmetic).trans transported
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.MulDivCached.native.range16_clean_refinement _ valid _

theorem range_lookup5
    (sourceValue : Fin 71 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.MulDivCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.MulDivCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.MulDivCached.native.assigned (Airbender.Compiler.HelperValidityNative.MulDivCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.MulDivCached.AuthoredLookupValid sourceValue) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.MulDivCached.native.rangeExpression5).Contains (Airbender.Compiler.CleanArithmeticNative.MulDivCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.MulDivCached.native.range16Queries.get ⟨5, by decide⟩
  have member := authored.2 query (List.get_mem Airbender.Compiler.LookupSourceNative.MulDivCached.native.range16Queries ⟨5, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.MulDivCached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.MulDivCached.native.field13_0.source.value (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.originalProjection)] := member nonzero
  have present : Airbender.Compiler.LookupNative.MulDivCached.native.field13_0.source ∈ Airbender.Compiler.QueryFrameNative.MulDivCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.MulDivCached.native.fields ⟨87, by decide⟩
  have transported := Airbender.Compiler.QueryFrameNative.MulDivCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.MulDivCached.native.field13_0.source present
  have same := (Airbender.Compiler.CleanArgumentsNative.MulDivCached.native.range_value5 physical data arithmetic).trans transported
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.MulDivCached.native.range16_clean_refinement _ valid _

theorem range_lookup6
    (sourceValue : Fin 71 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.MulDivCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.MulDivCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.MulDivCached.native.assigned (Airbender.Compiler.HelperValidityNative.MulDivCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.MulDivCached.AuthoredLookupValid sourceValue) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.MulDivCached.native.rangeExpression6).Contains (Airbender.Compiler.CleanArithmeticNative.MulDivCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.MulDivCached.native.range16Queries.get ⟨6, by decide⟩
  have member := authored.2 query (List.get_mem Airbender.Compiler.LookupSourceNative.MulDivCached.native.range16Queries ⟨6, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.MulDivCached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.MulDivCached.native.field14_0.source.value (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.originalProjection)] := member nonzero
  have present : Airbender.Compiler.LookupNative.MulDivCached.native.field14_0.source ∈ Airbender.Compiler.QueryFrameNative.MulDivCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.MulDivCached.native.fields ⟨88, by decide⟩
  have transported := Airbender.Compiler.QueryFrameNative.MulDivCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.MulDivCached.native.field14_0.source present
  have same := (Airbender.Compiler.CleanArgumentsNative.MulDivCached.native.range_value6 physical data arithmetic).trans transported
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.MulDivCached.native.range16_clean_refinement _ valid _

theorem range_lookup7
    (sourceValue : Fin 71 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.MulDivCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.MulDivCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.MulDivCached.native.assigned (Airbender.Compiler.HelperValidityNative.MulDivCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.MulDivCached.AuthoredLookupValid sourceValue) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.MulDivCached.native.rangeExpression7).Contains (Airbender.Compiler.CleanArithmeticNative.MulDivCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.MulDivCached.native.range16Queries.get ⟨7, by decide⟩
  have member := authored.2 query (List.get_mem Airbender.Compiler.LookupSourceNative.MulDivCached.native.range16Queries ⟨7, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.MulDivCached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.MulDivCached.native.field15_0.source.value (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.originalProjection)] := member nonzero
  have present : Airbender.Compiler.LookupNative.MulDivCached.native.field15_0.source ∈ Airbender.Compiler.QueryFrameNative.MulDivCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.MulDivCached.native.fields ⟨89, by decide⟩
  have transported := Airbender.Compiler.QueryFrameNative.MulDivCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.MulDivCached.native.field15_0.source present
  have same := (Airbender.Compiler.CleanArgumentsNative.MulDivCached.native.range_value7 physical data arithmetic).trans transported
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.MulDivCached.native.range16_clean_refinement _ valid _

theorem generic_lookup0
    (sourceValue : Fin 71 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.MulDivCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.MulDivCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.MulDivCached.native.assigned (Airbender.Compiler.HelperValidityNative.MulDivCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.MulDivCached.AuthoredLookupValid sourceValue) :
    fixedLookup0.Contains (Airbender.Compiler.CleanArithmeticNative.MulDivCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.MulDivCached.native.genericQueries.get ⟨0, by decide⟩
  have member := authored.1 query (List.get_mem Airbender.Compiler.LookupSourceNative.MulDivCached.native.genericQueries ⟨0, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  obtain ⟨setupRow, dataRow⟩ := member nonzero
  have tagProof := congrArg (fun entries : List Source.BaseField => entries.getD 8 0) dataRow
  change (1 : Source.BaseField) = Airbender.Compiler.MaterializedNative.MulDivCached.native.model.value setupRow (.generic 8) at tagProof
  have selected : Airbender.Compiler.FixedSetupNative.MulDiv.nativeSetup.value setupRow (.generic 8) = 1 := tagProof.symm
  have present0 : Airbender.Compiler.LookupNative.MulDivCached.native.field0_0.source ∈ Airbender.Compiler.QueryFrameNative.MulDivCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.MulDivCached.native.fields ⟨0, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.MulDivCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.MulDivCached.native.field0_0.source present0
  have sourceCell0 := congrArg (fun entries : List Source.BaseField => entries.getD 0 0) dataRow
  change Airbender.Compiler.LookupNative.MulDivCached.native.field0_0.source.value (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.originalProjection) = Airbender.Compiler.MaterializedNative.MulDivCached.native.model.value setupRow (.generic 0) at sourceCell0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.MulDivCached.native.part0.generic_value0_0 physical data arithmetic).trans (transported0.trans sourceCell0)
  have present1 : Airbender.Compiler.LookupNative.MulDivCached.native.field0_1.source ∈ Airbender.Compiler.QueryFrameNative.MulDivCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.MulDivCached.native.fields ⟨1, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.MulDivCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.MulDivCached.native.field0_1.source present1
  have sourceCell1 := congrArg (fun entries : List Source.BaseField => entries.getD 1 0) dataRow
  change Airbender.Compiler.LookupNative.MulDivCached.native.field0_1.source.value (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.originalProjection) = Airbender.Compiler.MaterializedNative.MulDivCached.native.model.value setupRow (.generic 1) at sourceCell1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.MulDivCached.native.part0.generic_value0_1 physical data arithmetic).trans (transported1.trans sourceCell1)
  apply clean_pair_lookup
  rw [same0, same1]
  exact Airbender.Compiler.FixedSetupNative.MulDiv.tag1_contains setupRow selected _

theorem generic_lookup1
    (sourceValue : Fin 71 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.MulDivCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.MulDivCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.MulDivCached.native.assigned (Airbender.Compiler.HelperValidityNative.MulDivCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.MulDivCached.AuthoredLookupValid sourceValue) :
    fixedLookup1.Contains (Airbender.Compiler.CleanArithmeticNative.MulDivCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.MulDivCached.native.genericQueries.get ⟨1, by decide⟩
  have member := authored.1 query (List.get_mem Airbender.Compiler.LookupSourceNative.MulDivCached.native.genericQueries ⟨1, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  obtain ⟨setupRow, dataRow⟩ := member nonzero
  have tagProof := congrArg (fun entries : List Source.BaseField => entries.getD 8 0) dataRow
  change (41 : Source.BaseField) = Airbender.Compiler.MaterializedNative.MulDivCached.native.model.value setupRow (.generic 8) at tagProof
  have selected : Airbender.Compiler.FixedSetupNative.MulDiv.nativeSetup.value setupRow (.generic 8) = 41 := tagProof.symm
  have present0 : Airbender.Compiler.LookupNative.MulDivCached.native.field1_0.source ∈ Airbender.Compiler.QueryFrameNative.MulDivCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.MulDivCached.native.fields ⟨9, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.MulDivCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.MulDivCached.native.field1_0.source present0
  have sourceCell0 := congrArg (fun entries : List Source.BaseField => entries.getD 0 0) dataRow
  change Airbender.Compiler.LookupNative.MulDivCached.native.field1_0.source.value (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.originalProjection) = Airbender.Compiler.MaterializedNative.MulDivCached.native.model.value setupRow (.generic 0) at sourceCell0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.MulDivCached.native.part0.generic_value1_0 physical data arithmetic).trans (transported0.trans sourceCell0)
  have present1 : Airbender.Compiler.LookupNative.MulDivCached.native.field1_1.source ∈ Airbender.Compiler.QueryFrameNative.MulDivCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.MulDivCached.native.fields ⟨10, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.MulDivCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.MulDivCached.native.field1_1.source present1
  have sourceCell1 := congrArg (fun entries : List Source.BaseField => entries.getD 1 0) dataRow
  change Airbender.Compiler.LookupNative.MulDivCached.native.field1_1.source.value (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.originalProjection) = Airbender.Compiler.MaterializedNative.MulDivCached.native.model.value setupRow (.generic 1) at sourceCell1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.MulDivCached.native.part0.generic_value1_1 physical data arithmetic).trans (transported1.trans sourceCell1)
  apply clean_pair_lookup
  rw [same0, same1]
  exact Airbender.Compiler.FixedSetupNative.MulDiv.tag41_contains setupRow selected _

theorem generic_lookup2
    (sourceValue : Fin 71 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.MulDivCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.MulDivCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.MulDivCached.native.assigned (Airbender.Compiler.HelperValidityNative.MulDivCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.MulDivCached.AuthoredLookupValid sourceValue) :
    fixedLookup2.Contains (Airbender.Compiler.CleanArithmeticNative.MulDivCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.MulDivCached.native.genericQueries.get ⟨2, by decide⟩
  have member := authored.1 query (List.get_mem Airbender.Compiler.LookupSourceNative.MulDivCached.native.genericQueries ⟨2, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  obtain ⟨setupRow, dataRow⟩ := member nonzero
  have tagProof := congrArg (fun entries : List Source.BaseField => entries.getD 8 0) dataRow
  change (41 : Source.BaseField) = Airbender.Compiler.MaterializedNative.MulDivCached.native.model.value setupRow (.generic 8) at tagProof
  have selected : Airbender.Compiler.FixedSetupNative.MulDiv.nativeSetup.value setupRow (.generic 8) = 41 := tagProof.symm
  have present0 : Airbender.Compiler.LookupNative.MulDivCached.native.field2_0.source ∈ Airbender.Compiler.QueryFrameNative.MulDivCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.MulDivCached.native.fields ⟨18, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.MulDivCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.MulDivCached.native.field2_0.source present0
  have sourceCell0 := congrArg (fun entries : List Source.BaseField => entries.getD 0 0) dataRow
  change Airbender.Compiler.LookupNative.MulDivCached.native.field2_0.source.value (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.originalProjection) = Airbender.Compiler.MaterializedNative.MulDivCached.native.model.value setupRow (.generic 0) at sourceCell0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.MulDivCached.native.part0.generic_value2_0 physical data arithmetic).trans (transported0.trans sourceCell0)
  have present1 : Airbender.Compiler.LookupNative.MulDivCached.native.field2_1.source ∈ Airbender.Compiler.QueryFrameNative.MulDivCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.MulDivCached.native.fields ⟨19, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.MulDivCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.MulDivCached.native.field2_1.source present1
  have sourceCell1 := congrArg (fun entries : List Source.BaseField => entries.getD 1 0) dataRow
  change Airbender.Compiler.LookupNative.MulDivCached.native.field2_1.source.value (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.originalProjection) = Airbender.Compiler.MaterializedNative.MulDivCached.native.model.value setupRow (.generic 1) at sourceCell1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.MulDivCached.native.part0.generic_value2_1 physical data arithmetic).trans (transported1.trans sourceCell1)
  apply clean_pair_lookup
  rw [same0, same1]
  exact Airbender.Compiler.FixedSetupNative.MulDiv.tag41_contains setupRow selected _

theorem generic_lookup3
    (sourceValue : Fin 71 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.MulDivCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.MulDivCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.MulDivCached.native.assigned (Airbender.Compiler.HelperValidityNative.MulDivCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.MulDivCached.AuthoredLookupValid sourceValue) :
    fixedLookup3.Contains (Airbender.Compiler.CleanArithmeticNative.MulDivCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.MulDivCached.native.genericQueries.get ⟨3, by decide⟩
  have member := authored.1 query (List.get_mem Airbender.Compiler.LookupSourceNative.MulDivCached.native.genericQueries ⟨3, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  obtain ⟨setupRow, dataRow⟩ := member nonzero
  have tagProof := congrArg (fun entries : List Source.BaseField => entries.getD 8 0) dataRow
  change (26 : Source.BaseField) = Airbender.Compiler.MaterializedNative.MulDivCached.native.model.value setupRow (.generic 8) at tagProof
  have selected : Airbender.Compiler.FixedSetupNative.MulDiv.nativeSetup.value setupRow (.generic 8) = 26 := tagProof.symm
  have present0 : Airbender.Compiler.LookupNative.MulDivCached.native.field3_0.source ∈ Airbender.Compiler.QueryFrameNative.MulDivCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.MulDivCached.native.fields ⟨27, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.MulDivCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.MulDivCached.native.field3_0.source present0
  have sourceCell0 := congrArg (fun entries : List Source.BaseField => entries.getD 0 0) dataRow
  change Airbender.Compiler.LookupNative.MulDivCached.native.field3_0.source.value (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.originalProjection) = Airbender.Compiler.MaterializedNative.MulDivCached.native.model.value setupRow (.generic 0) at sourceCell0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.MulDivCached.native.part0.generic_value3_0 physical data arithmetic).trans (transported0.trans sourceCell0)
  apply Verification.range13_contains
  rw [same0]
  exact Airbender.Compiler.FixedSetupNative.MulDiv.range13_value_bound setupRow selected

theorem generic_lookup4
    (sourceValue : Fin 71 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.MulDivCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.MulDivCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.MulDivCached.native.assigned (Airbender.Compiler.HelperValidityNative.MulDivCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.MulDivCached.AuthoredLookupValid sourceValue) :
    fixedLookup4.Contains (Airbender.Compiler.CleanArithmeticNative.MulDivCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.MulDivCached.native.genericQueries.get ⟨4, by decide⟩
  have member := authored.1 query (List.get_mem Airbender.Compiler.LookupSourceNative.MulDivCached.native.genericQueries ⟨4, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  obtain ⟨setupRow, dataRow⟩ := member nonzero
  have tagProof := congrArg (fun entries : List Source.BaseField => entries.getD 8 0) dataRow
  change (26 : Source.BaseField) = Airbender.Compiler.MaterializedNative.MulDivCached.native.model.value setupRow (.generic 8) at tagProof
  have selected : Airbender.Compiler.FixedSetupNative.MulDiv.nativeSetup.value setupRow (.generic 8) = 26 := tagProof.symm
  have present0 : Airbender.Compiler.LookupNative.MulDivCached.native.field4_0.source ∈ Airbender.Compiler.QueryFrameNative.MulDivCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.MulDivCached.native.fields ⟨36, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.MulDivCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.MulDivCached.native.field4_0.source present0
  have sourceCell0 := congrArg (fun entries : List Source.BaseField => entries.getD 0 0) dataRow
  change Airbender.Compiler.LookupNative.MulDivCached.native.field4_0.source.value (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.originalProjection) = Airbender.Compiler.MaterializedNative.MulDivCached.native.model.value setupRow (.generic 0) at sourceCell0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.MulDivCached.native.part0.generic_value4_0 physical data arithmetic).trans (transported0.trans sourceCell0)
  apply Verification.range13_contains
  rw [same0]
  exact Airbender.Compiler.FixedSetupNative.MulDiv.range13_value_bound setupRow selected

theorem generic_lookup5
    (sourceValue : Fin 71 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.MulDivCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.MulDivCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.MulDivCached.native.assigned (Airbender.Compiler.HelperValidityNative.MulDivCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.MulDivCached.AuthoredLookupValid sourceValue) :
    fixedLookup5.Contains (Airbender.Compiler.CleanArithmeticNative.MulDivCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.MulDivCached.native.genericQueries.get ⟨5, by decide⟩
  have member := authored.1 query (List.get_mem Airbender.Compiler.LookupSourceNative.MulDivCached.native.genericQueries ⟨5, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  obtain ⟨setupRow, dataRow⟩ := member nonzero
  have tagProof := congrArg (fun entries : List Source.BaseField => entries.getD 8 0) dataRow
  change (26 : Source.BaseField) = Airbender.Compiler.MaterializedNative.MulDivCached.native.model.value setupRow (.generic 8) at tagProof
  have selected : Airbender.Compiler.FixedSetupNative.MulDiv.nativeSetup.value setupRow (.generic 8) = 26 := tagProof.symm
  have present0 : Airbender.Compiler.LookupNative.MulDivCached.native.field5_0.source ∈ Airbender.Compiler.QueryFrameNative.MulDivCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.MulDivCached.native.fields ⟨45, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.MulDivCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.MulDivCached.native.field5_0.source present0
  have sourceCell0 := congrArg (fun entries : List Source.BaseField => entries.getD 0 0) dataRow
  change Airbender.Compiler.LookupNative.MulDivCached.native.field5_0.source.value (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.originalProjection) = Airbender.Compiler.MaterializedNative.MulDivCached.native.model.value setupRow (.generic 0) at sourceCell0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.MulDivCached.native.part0.generic_value5_0 physical data arithmetic).trans (transported0.trans sourceCell0)
  apply Verification.range13_contains
  rw [same0]
  exact Airbender.Compiler.FixedSetupNative.MulDiv.range13_value_bound setupRow selected

theorem generic_lookup6
    (sourceValue : Fin 71 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.MulDivCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.MulDivCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.MulDivCached.native.assigned (Airbender.Compiler.HelperValidityNative.MulDivCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.MulDivCached.AuthoredLookupValid sourceValue) :
    fixedLookup6.Contains (Airbender.Compiler.CleanArithmeticNative.MulDivCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.MulDivCached.native.genericQueries.get ⟨6, by decide⟩
  have member := authored.1 query (List.get_mem Airbender.Compiler.LookupSourceNative.MulDivCached.native.genericQueries ⟨6, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  obtain ⟨setupRow, dataRow⟩ := member nonzero
  have tagProof := congrArg (fun entries : List Source.BaseField => entries.getD 8 0) dataRow
  change (41 : Source.BaseField) = Airbender.Compiler.MaterializedNative.MulDivCached.native.model.value setupRow (.generic 8) at tagProof
  have selected : Airbender.Compiler.FixedSetupNative.MulDiv.nativeSetup.value setupRow (.generic 8) = 41 := tagProof.symm
  have present0 : Airbender.Compiler.LookupNative.MulDivCached.native.field6_0.source ∈ Airbender.Compiler.QueryFrameNative.MulDivCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.MulDivCached.native.fields ⟨54, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.MulDivCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.MulDivCached.native.field6_0.source present0
  have sourceCell0 := congrArg (fun entries : List Source.BaseField => entries.getD 0 0) dataRow
  change Airbender.Compiler.LookupNative.MulDivCached.native.field6_0.source.value (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.originalProjection) = Airbender.Compiler.MaterializedNative.MulDivCached.native.model.value setupRow (.generic 0) at sourceCell0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.MulDivCached.native.part0.generic_value6_0 physical data arithmetic).trans (transported0.trans sourceCell0)
  have present1 : Airbender.Compiler.LookupNative.MulDivCached.native.field6_1.source ∈ Airbender.Compiler.QueryFrameNative.MulDivCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.MulDivCached.native.fields ⟨55, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.MulDivCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.MulDivCached.native.field6_1.source present1
  have sourceCell1 := congrArg (fun entries : List Source.BaseField => entries.getD 1 0) dataRow
  change Airbender.Compiler.LookupNative.MulDivCached.native.field6_1.source.value (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.originalProjection) = Airbender.Compiler.MaterializedNative.MulDivCached.native.model.value setupRow (.generic 1) at sourceCell1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.MulDivCached.native.part0.generic_value6_1 physical data arithmetic).trans (transported1.trans sourceCell1)
  apply clean_pair_lookup
  rw [same0, same1]
  exact Airbender.Compiler.FixedSetupNative.MulDiv.tag41_contains setupRow selected _

theorem generic_lookup7
    (sourceValue : Fin 71 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.MulDivCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.MulDivCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.MulDivCached.native.assigned (Airbender.Compiler.HelperValidityNative.MulDivCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.MulDivCached.AuthoredLookupValid sourceValue) :
    fixedLookup7.Contains (Airbender.Compiler.CleanArithmeticNative.MulDivCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.MulDivCached.native.genericQueries.get ⟨7, by decide⟩
  have member := authored.1 query (List.get_mem Airbender.Compiler.LookupSourceNative.MulDivCached.native.genericQueries ⟨7, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  obtain ⟨setupRow, dataRow⟩ := member nonzero
  have tagProof := congrArg (fun entries : List Source.BaseField => entries.getD 8 0) dataRow
  change (41 : Source.BaseField) = Airbender.Compiler.MaterializedNative.MulDivCached.native.model.value setupRow (.generic 8) at tagProof
  have selected : Airbender.Compiler.FixedSetupNative.MulDiv.nativeSetup.value setupRow (.generic 8) = 41 := tagProof.symm
  have present0 : Airbender.Compiler.LookupNative.MulDivCached.native.field7_0.source ∈ Airbender.Compiler.QueryFrameNative.MulDivCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.MulDivCached.native.fields ⟨63, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.MulDivCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.MulDivCached.native.field7_0.source present0
  have sourceCell0 := congrArg (fun entries : List Source.BaseField => entries.getD 0 0) dataRow
  change Airbender.Compiler.LookupNative.MulDivCached.native.field7_0.source.value (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.originalProjection) = Airbender.Compiler.MaterializedNative.MulDivCached.native.model.value setupRow (.generic 0) at sourceCell0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.MulDivCached.native.part0.generic_value7_0 physical data arithmetic).trans (transported0.trans sourceCell0)
  have present1 : Airbender.Compiler.LookupNative.MulDivCached.native.field7_1.source ∈ Airbender.Compiler.QueryFrameNative.MulDivCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.MulDivCached.native.fields ⟨64, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.MulDivCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.MulDivCached.native.field7_1.source present1
  have sourceCell1 := congrArg (fun entries : List Source.BaseField => entries.getD 1 0) dataRow
  change Airbender.Compiler.LookupNative.MulDivCached.native.field7_1.source.value (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.originalProjection) = Airbender.Compiler.MaterializedNative.MulDivCached.native.model.value setupRow (.generic 1) at sourceCell1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.MulDivCached.native.part0.generic_value7_1 physical data arithmetic).trans (transported1.trans sourceCell1)
  apply clean_pair_lookup
  rw [same0, same1]
  exact Airbender.Compiler.FixedSetupNative.MulDiv.tag41_contains setupRow selected _

theorem retained_clock_from_source
    (sourceValue : Fin 71 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.MulDivCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.MulDivCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.MulDivCached.native.assigned (Airbender.Compiler.HelperValidityNative.MulDivCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) = 0)
    (helpers : ∀ field ∈ Airbender.Compiler.HelperNative.MulDivCached.native.fields, (field.value (Airbender.Compiler.HelperNative.MulDivCached.native.sourceValues physical)).val < 524288)
    (authored : Airbender.Compiler.MaterializedWitnessNative.MulDivCached.AuthoredLookupValid sourceValue) :
    FlatOperation.ConstraintsHoldFlat (Airbender.Compiler.CleanArithmeticNative.MulDivCached.native.environment physical data) (Airbender.MulDiv.clockConstraints (p := babyBearModulus)) := by
  apply Airbender.Compiler.CleanLinksNative.MulDivCached.retained_clock_constraints physical data arithmetic
  rw [clock_lookup_inventory]
  exact PredicateChecks.all (PredicateChecks.cons (range_lookup0 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (range_lookup1 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (range_lookup2 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (range_lookup3 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (range_lookup4 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (range_lookup5 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (range_lookup6 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (range_lookup7 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (generic_lookup0 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (generic_lookup1 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (generic_lookup2 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (generic_lookup3 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (generic_lookup4 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (generic_lookup5 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (generic_lookup6 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (generic_lookup7 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.MulDivCached.native.timestampExpression0 (Airbender.Compiler.CleanArithmeticNative.MulDivCached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.MulDivCached.native.timestamp_bound0 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.MulDivCached.native.timestampExpression1 (Airbender.Compiler.CleanArithmeticNative.MulDivCached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.MulDivCached.native.timestamp_bound1 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.MulDivCached.native.timestampExpression2 (Airbender.Compiler.CleanArithmeticNative.MulDivCached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.MulDivCached.native.timestamp_bound2 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.MulDivCached.native.timestampExpression3 (Airbender.Compiler.CleanArithmeticNative.MulDivCached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.MulDivCached.native.timestamp_bound3 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.MulDivCached.native.timestampExpression4 (Airbender.Compiler.CleanArithmeticNative.MulDivCached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.MulDivCached.native.timestamp_bound4 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.MulDivCached.native.timestampExpression5 (Airbender.Compiler.CleanArithmeticNative.MulDivCached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.MulDivCached.native.timestamp_bound5 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.MulDivCached.native.timestampExpression6 (Airbender.Compiler.CleanArithmeticNative.MulDivCached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.MulDivCached.native.timestamp_bound6 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.MulDivCached.native.timestampExpression7 (Airbender.Compiler.CleanArithmeticNative.MulDivCached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.MulDivCached.native.timestamp_bound7 physical data arithmetic helpers)) PredicateChecks.nil))))))))))))))))))))))))

end Airbender.Compiler.CleanClosedNative.MulDivCached
