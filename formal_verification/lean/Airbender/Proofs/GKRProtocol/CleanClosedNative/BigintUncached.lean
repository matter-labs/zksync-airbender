import Airbender.Proofs.GKRProtocol.CleanClosedParts.BigintUncached.Part0
import Airbender.Proofs.GKRProtocol.CleanClosedParts.BigintUncached.Part1
import Airbender.Proofs.GKRProtocol.CleanClosedParts.BigintUncached.Part2
import Airbender.Proofs.GKRProtocol.CleanClosedParts.BigintUncached.Part3
import Airbender.Proofs.GKRProtocol.CleanClosedParts.BigintUncached.Part4
import Airbender.Proofs.GKRProtocol.CleanClosedParts.BigintUncached.Part5
import Airbender.Proofs.GKRProtocol.CleanClosedParts.BigintUncached.Part6
import Airbender.Proofs.GKRProtocol.CleanClosedParts.BigintUncached.Part7

namespace Airbender.Compiler.CleanClosedNative.BigintUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

theorem range_lookup0
    (sourceValue : Fin 276 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BigintUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BigintUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BigintUncached.native.assigned (Airbender.Compiler.HelperValidityNative.BigintUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BigintUncached.AuthoredLookupValid sourceValue) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression0).Contains (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BigintUncached.native.range16Queries.get ⟨0, by decide⟩
  have member := authored.2 query (List.get_mem Airbender.Compiler.LookupSourceNative.BigintUncached.native.range16Queries ⟨0, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.BigintUncached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.BigintUncached.native.field61_0.source.value (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.originalProjection)] := member nonzero
  have present : Airbender.Compiler.LookupNative.BigintUncached.native.field61_0.source ∈ Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields ⟨183, by decide⟩
  have transported := Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintUncached.native.field61_0.source present
  have same := (Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.range_value0 physical data arithmetic).trans transported
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.BigintUncached.native.range16_clean_refinement _ valid _

theorem range_lookup1
    (sourceValue : Fin 276 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BigintUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BigintUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BigintUncached.native.assigned (Airbender.Compiler.HelperValidityNative.BigintUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BigintUncached.AuthoredLookupValid sourceValue) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression1).Contains (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BigintUncached.native.range16Queries.get ⟨1, by decide⟩
  have member := authored.2 query (List.get_mem Airbender.Compiler.LookupSourceNative.BigintUncached.native.range16Queries ⟨1, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.BigintUncached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.BigintUncached.native.field62_0.source.value (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.originalProjection)] := member nonzero
  have present : Airbender.Compiler.LookupNative.BigintUncached.native.field62_0.source ∈ Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields ⟨184, by decide⟩
  have transported := Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintUncached.native.field62_0.source present
  have same := (Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.range_value1 physical data arithmetic).trans transported
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.BigintUncached.native.range16_clean_refinement _ valid _

theorem range_lookup2
    (sourceValue : Fin 276 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BigintUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BigintUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BigintUncached.native.assigned (Airbender.Compiler.HelperValidityNative.BigintUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BigintUncached.AuthoredLookupValid sourceValue) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression2).Contains (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BigintUncached.native.range16Queries.get ⟨2, by decide⟩
  have member := authored.2 query (List.get_mem Airbender.Compiler.LookupSourceNative.BigintUncached.native.range16Queries ⟨2, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.BigintUncached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.BigintUncached.native.field63_0.source.value (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.originalProjection)] := member nonzero
  have present : Airbender.Compiler.LookupNative.BigintUncached.native.field63_0.source ∈ Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields ⟨185, by decide⟩
  have transported := Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintUncached.native.field63_0.source present
  have same := (Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.range_value2 physical data arithmetic).trans transported
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.BigintUncached.native.range16_clean_refinement _ valid _

theorem range_lookup3
    (sourceValue : Fin 276 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BigintUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BigintUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BigintUncached.native.assigned (Airbender.Compiler.HelperValidityNative.BigintUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BigintUncached.AuthoredLookupValid sourceValue) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression3).Contains (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BigintUncached.native.range16Queries.get ⟨3, by decide⟩
  have member := authored.2 query (List.get_mem Airbender.Compiler.LookupSourceNative.BigintUncached.native.range16Queries ⟨3, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.BigintUncached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.BigintUncached.native.field64_0.source.value (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.originalProjection)] := member nonzero
  have present : Airbender.Compiler.LookupNative.BigintUncached.native.field64_0.source ∈ Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields ⟨186, by decide⟩
  have transported := Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintUncached.native.field64_0.source present
  have same := (Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.range_value3 physical data arithmetic).trans transported
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.BigintUncached.native.range16_clean_refinement _ valid _

theorem range_lookup4
    (sourceValue : Fin 276 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BigintUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BigintUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BigintUncached.native.assigned (Airbender.Compiler.HelperValidityNative.BigintUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BigintUncached.AuthoredLookupValid sourceValue) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression4).Contains (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BigintUncached.native.range16Queries.get ⟨4, by decide⟩
  have member := authored.2 query (List.get_mem Airbender.Compiler.LookupSourceNative.BigintUncached.native.range16Queries ⟨4, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.BigintUncached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.BigintUncached.native.field65_0.source.value (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.originalProjection)] := member nonzero
  have present : Airbender.Compiler.LookupNative.BigintUncached.native.field65_0.source ∈ Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields ⟨187, by decide⟩
  have transported := Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintUncached.native.field65_0.source present
  have same := (Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.range_value4 physical data arithmetic).trans transported
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.BigintUncached.native.range16_clean_refinement _ valid _

theorem range_lookup5
    (sourceValue : Fin 276 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BigintUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BigintUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BigintUncached.native.assigned (Airbender.Compiler.HelperValidityNative.BigintUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BigintUncached.AuthoredLookupValid sourceValue) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression5).Contains (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BigintUncached.native.range16Queries.get ⟨5, by decide⟩
  have member := authored.2 query (List.get_mem Airbender.Compiler.LookupSourceNative.BigintUncached.native.range16Queries ⟨5, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.BigintUncached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.BigintUncached.native.field66_0.source.value (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.originalProjection)] := member nonzero
  have present : Airbender.Compiler.LookupNative.BigintUncached.native.field66_0.source ∈ Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields ⟨188, by decide⟩
  have transported := Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintUncached.native.field66_0.source present
  have same := (Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.range_value5 physical data arithmetic).trans transported
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.BigintUncached.native.range16_clean_refinement _ valid _

theorem range_lookup6
    (sourceValue : Fin 276 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BigintUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BigintUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BigintUncached.native.assigned (Airbender.Compiler.HelperValidityNative.BigintUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BigintUncached.AuthoredLookupValid sourceValue) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression6).Contains (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BigintUncached.native.range16Queries.get ⟨6, by decide⟩
  have member := authored.2 query (List.get_mem Airbender.Compiler.LookupSourceNative.BigintUncached.native.range16Queries ⟨6, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.BigintUncached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.BigintUncached.native.field67_0.source.value (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.originalProjection)] := member nonzero
  have present : Airbender.Compiler.LookupNative.BigintUncached.native.field67_0.source ∈ Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields ⟨189, by decide⟩
  have transported := Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintUncached.native.field67_0.source present
  have same := (Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.range_value6 physical data arithmetic).trans transported
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.BigintUncached.native.range16_clean_refinement _ valid _

theorem range_lookup7
    (sourceValue : Fin 276 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BigintUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BigintUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BigintUncached.native.assigned (Airbender.Compiler.HelperValidityNative.BigintUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BigintUncached.AuthoredLookupValid sourceValue) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression7).Contains (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BigintUncached.native.range16Queries.get ⟨7, by decide⟩
  have member := authored.2 query (List.get_mem Airbender.Compiler.LookupSourceNative.BigintUncached.native.range16Queries ⟨7, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.BigintUncached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.BigintUncached.native.field68_0.source.value (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.originalProjection)] := member nonzero
  have present : Airbender.Compiler.LookupNative.BigintUncached.native.field68_0.source ∈ Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields ⟨190, by decide⟩
  have transported := Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintUncached.native.field68_0.source present
  have same := (Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.range_value7 physical data arithmetic).trans transported
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.BigintUncached.native.range16_clean_refinement _ valid _

theorem range_lookup8
    (sourceValue : Fin 276 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BigintUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BigintUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BigintUncached.native.assigned (Airbender.Compiler.HelperValidityNative.BigintUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BigintUncached.AuthoredLookupValid sourceValue) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression8).Contains (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BigintUncached.native.range16Queries.get ⟨8, by decide⟩
  have member := authored.2 query (List.get_mem Airbender.Compiler.LookupSourceNative.BigintUncached.native.range16Queries ⟨8, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.BigintUncached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.BigintUncached.native.field69_0.source.value (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.originalProjection)] := member nonzero
  have present : Airbender.Compiler.LookupNative.BigintUncached.native.field69_0.source ∈ Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields ⟨191, by decide⟩
  have transported := Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintUncached.native.field69_0.source present
  have same := (Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.range_value8 physical data arithmetic).trans transported
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.BigintUncached.native.range16_clean_refinement _ valid _

theorem range_lookup9
    (sourceValue : Fin 276 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BigintUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BigintUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BigintUncached.native.assigned (Airbender.Compiler.HelperValidityNative.BigintUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BigintUncached.AuthoredLookupValid sourceValue) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression9).Contains (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BigintUncached.native.range16Queries.get ⟨9, by decide⟩
  have member := authored.2 query (List.get_mem Airbender.Compiler.LookupSourceNative.BigintUncached.native.range16Queries ⟨9, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.BigintUncached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.BigintUncached.native.field70_0.source.value (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.originalProjection)] := member nonzero
  have present : Airbender.Compiler.LookupNative.BigintUncached.native.field70_0.source ∈ Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields ⟨192, by decide⟩
  have transported := Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintUncached.native.field70_0.source present
  have same := (Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.range_value9 physical data arithmetic).trans transported
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.BigintUncached.native.range16_clean_refinement _ valid _

theorem range_lookup10
    (sourceValue : Fin 276 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BigintUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BigintUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BigintUncached.native.assigned (Airbender.Compiler.HelperValidityNative.BigintUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BigintUncached.AuthoredLookupValid sourceValue) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression10).Contains (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BigintUncached.native.range16Queries.get ⟨10, by decide⟩
  have member := authored.2 query (List.get_mem Airbender.Compiler.LookupSourceNative.BigintUncached.native.range16Queries ⟨10, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.BigintUncached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.BigintUncached.native.field71_0.source.value (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.originalProjection)] := member nonzero
  have present : Airbender.Compiler.LookupNative.BigintUncached.native.field71_0.source ∈ Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields ⟨193, by decide⟩
  have transported := Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintUncached.native.field71_0.source present
  have same := (Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.range_value10 physical data arithmetic).trans transported
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.BigintUncached.native.range16_clean_refinement _ valid _

theorem range_lookup11
    (sourceValue : Fin 276 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BigintUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BigintUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BigintUncached.native.assigned (Airbender.Compiler.HelperValidityNative.BigintUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BigintUncached.AuthoredLookupValid sourceValue) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression11).Contains (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BigintUncached.native.range16Queries.get ⟨11, by decide⟩
  have member := authored.2 query (List.get_mem Airbender.Compiler.LookupSourceNative.BigintUncached.native.range16Queries ⟨11, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.BigintUncached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.BigintUncached.native.field72_0.source.value (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.originalProjection)] := member nonzero
  have present : Airbender.Compiler.LookupNative.BigintUncached.native.field72_0.source ∈ Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields ⟨194, by decide⟩
  have transported := Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintUncached.native.field72_0.source present
  have same := (Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.range_value11 physical data arithmetic).trans transported
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.BigintUncached.native.range16_clean_refinement _ valid _

theorem range_lookup12
    (sourceValue : Fin 276 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BigintUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BigintUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BigintUncached.native.assigned (Airbender.Compiler.HelperValidityNative.BigintUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BigintUncached.AuthoredLookupValid sourceValue) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression12).Contains (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BigintUncached.native.range16Queries.get ⟨12, by decide⟩
  have member := authored.2 query (List.get_mem Airbender.Compiler.LookupSourceNative.BigintUncached.native.range16Queries ⟨12, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.BigintUncached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.BigintUncached.native.field73_0.source.value (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.originalProjection)] := member nonzero
  have present : Airbender.Compiler.LookupNative.BigintUncached.native.field73_0.source ∈ Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields ⟨195, by decide⟩
  have transported := Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintUncached.native.field73_0.source present
  have same := (Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.range_value12 physical data arithmetic).trans transported
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.BigintUncached.native.range16_clean_refinement _ valid _

theorem range_lookup13
    (sourceValue : Fin 276 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BigintUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BigintUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BigintUncached.native.assigned (Airbender.Compiler.HelperValidityNative.BigintUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BigintUncached.AuthoredLookupValid sourceValue) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression13).Contains (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BigintUncached.native.range16Queries.get ⟨13, by decide⟩
  have member := authored.2 query (List.get_mem Airbender.Compiler.LookupSourceNative.BigintUncached.native.range16Queries ⟨13, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.BigintUncached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.BigintUncached.native.field74_0.source.value (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.originalProjection)] := member nonzero
  have present : Airbender.Compiler.LookupNative.BigintUncached.native.field74_0.source ∈ Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields ⟨196, by decide⟩
  have transported := Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintUncached.native.field74_0.source present
  have same := (Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.range_value13 physical data arithmetic).trans transported
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.BigintUncached.native.range16_clean_refinement _ valid _

theorem range_lookup14
    (sourceValue : Fin 276 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BigintUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BigintUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BigintUncached.native.assigned (Airbender.Compiler.HelperValidityNative.BigintUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BigintUncached.AuthoredLookupValid sourceValue) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression14).Contains (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BigintUncached.native.range16Queries.get ⟨14, by decide⟩
  have member := authored.2 query (List.get_mem Airbender.Compiler.LookupSourceNative.BigintUncached.native.range16Queries ⟨14, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.BigintUncached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.BigintUncached.native.field75_0.source.value (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.originalProjection)] := member nonzero
  have present : Airbender.Compiler.LookupNative.BigintUncached.native.field75_0.source ∈ Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields ⟨197, by decide⟩
  have transported := Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintUncached.native.field75_0.source present
  have same := (Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.range_value14 physical data arithmetic).trans transported
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.BigintUncached.native.range16_clean_refinement _ valid _

theorem range_lookup15
    (sourceValue : Fin 276 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BigintUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BigintUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BigintUncached.native.assigned (Airbender.Compiler.HelperValidityNative.BigintUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BigintUncached.AuthoredLookupValid sourceValue) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression15).Contains (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BigintUncached.native.range16Queries.get ⟨15, by decide⟩
  have member := authored.2 query (List.get_mem Airbender.Compiler.LookupSourceNative.BigintUncached.native.range16Queries ⟨15, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.BigintUncached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.BigintUncached.native.field76_0.source.value (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.originalProjection)] := member nonzero
  have present : Airbender.Compiler.LookupNative.BigintUncached.native.field76_0.source ∈ Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields ⟨198, by decide⟩
  have transported := Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintUncached.native.field76_0.source present
  have same := (Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.range_value15 physical data arithmetic).trans transported
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.BigintUncached.native.range16_clean_refinement _ valid _

theorem range_lookup16
    (sourceValue : Fin 276 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BigintUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BigintUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BigintUncached.native.assigned (Airbender.Compiler.HelperValidityNative.BigintUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BigintUncached.AuthoredLookupValid sourceValue) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression16).Contains (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BigintUncached.native.range16Queries.get ⟨16, by decide⟩
  have member := authored.2 query (List.get_mem Airbender.Compiler.LookupSourceNative.BigintUncached.native.range16Queries ⟨16, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.BigintUncached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.BigintUncached.native.field77_0.source.value (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.originalProjection)] := member nonzero
  have present : Airbender.Compiler.LookupNative.BigintUncached.native.field77_0.source ∈ Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields ⟨199, by decide⟩
  have transported := Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintUncached.native.field77_0.source present
  have same := (Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.range_value16 physical data arithmetic).trans transported
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.BigintUncached.native.range16_clean_refinement _ valid _

theorem range_lookup17
    (sourceValue : Fin 276 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BigintUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BigintUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BigintUncached.native.assigned (Airbender.Compiler.HelperValidityNative.BigintUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BigintUncached.AuthoredLookupValid sourceValue) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression17).Contains (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BigintUncached.native.range16Queries.get ⟨17, by decide⟩
  have member := authored.2 query (List.get_mem Airbender.Compiler.LookupSourceNative.BigintUncached.native.range16Queries ⟨17, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.BigintUncached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.BigintUncached.native.field78_0.source.value (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.originalProjection)] := member nonzero
  have present : Airbender.Compiler.LookupNative.BigintUncached.native.field78_0.source ∈ Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields ⟨200, by decide⟩
  have transported := Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintUncached.native.field78_0.source present
  have same := (Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.range_value17 physical data arithmetic).trans transported
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.BigintUncached.native.range16_clean_refinement _ valid _

theorem range_lookup18
    (sourceValue : Fin 276 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BigintUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BigintUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BigintUncached.native.assigned (Airbender.Compiler.HelperValidityNative.BigintUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BigintUncached.AuthoredLookupValid sourceValue) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression18).Contains (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BigintUncached.native.range16Queries.get ⟨18, by decide⟩
  have member := authored.2 query (List.get_mem Airbender.Compiler.LookupSourceNative.BigintUncached.native.range16Queries ⟨18, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.BigintUncached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.BigintUncached.native.field79_0.source.value (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.originalProjection)] := member nonzero
  have present : Airbender.Compiler.LookupNative.BigintUncached.native.field79_0.source ∈ Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields ⟨201, by decide⟩
  have transported := Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintUncached.native.field79_0.source present
  have same := (Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.range_value18 physical data arithmetic).trans transported
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.BigintUncached.native.range16_clean_refinement _ valid _

theorem range_lookup19
    (sourceValue : Fin 276 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BigintUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BigintUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BigintUncached.native.assigned (Airbender.Compiler.HelperValidityNative.BigintUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BigintUncached.AuthoredLookupValid sourceValue) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression19).Contains (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BigintUncached.native.range16Queries.get ⟨19, by decide⟩
  have member := authored.2 query (List.get_mem Airbender.Compiler.LookupSourceNative.BigintUncached.native.range16Queries ⟨19, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.BigintUncached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.BigintUncached.native.field80_0.source.value (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.originalProjection)] := member nonzero
  have present : Airbender.Compiler.LookupNative.BigintUncached.native.field80_0.source ∈ Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields ⟨202, by decide⟩
  have transported := Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintUncached.native.field80_0.source present
  have same := (Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.range_value19 physical data arithmetic).trans transported
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.BigintUncached.native.range16_clean_refinement _ valid _

theorem range_lookup20
    (sourceValue : Fin 276 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BigintUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BigintUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BigintUncached.native.assigned (Airbender.Compiler.HelperValidityNative.BigintUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BigintUncached.AuthoredLookupValid sourceValue) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression20).Contains (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BigintUncached.native.range16Queries.get ⟨20, by decide⟩
  have member := authored.2 query (List.get_mem Airbender.Compiler.LookupSourceNative.BigintUncached.native.range16Queries ⟨20, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.BigintUncached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.BigintUncached.native.field81_0.source.value (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.originalProjection)] := member nonzero
  have present : Airbender.Compiler.LookupNative.BigintUncached.native.field81_0.source ∈ Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields ⟨203, by decide⟩
  have transported := Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintUncached.native.field81_0.source present
  have same := (Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.range_value20 physical data arithmetic).trans transported
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.BigintUncached.native.range16_clean_refinement _ valid _

theorem range_lookup21
    (sourceValue : Fin 276 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BigintUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BigintUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BigintUncached.native.assigned (Airbender.Compiler.HelperValidityNative.BigintUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BigintUncached.AuthoredLookupValid sourceValue) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression21).Contains (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BigintUncached.native.range16Queries.get ⟨21, by decide⟩
  have member := authored.2 query (List.get_mem Airbender.Compiler.LookupSourceNative.BigintUncached.native.range16Queries ⟨21, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.BigintUncached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.BigintUncached.native.field82_0.source.value (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.originalProjection)] := member nonzero
  have present : Airbender.Compiler.LookupNative.BigintUncached.native.field82_0.source ∈ Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields ⟨204, by decide⟩
  have transported := Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintUncached.native.field82_0.source present
  have same := (Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.range_value21 physical data arithmetic).trans transported
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.BigintUncached.native.range16_clean_refinement _ valid _

theorem range_lookup22
    (sourceValue : Fin 276 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BigintUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BigintUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BigintUncached.native.assigned (Airbender.Compiler.HelperValidityNative.BigintUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BigintUncached.AuthoredLookupValid sourceValue) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression22).Contains (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BigintUncached.native.range16Queries.get ⟨22, by decide⟩
  have member := authored.2 query (List.get_mem Airbender.Compiler.LookupSourceNative.BigintUncached.native.range16Queries ⟨22, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.BigintUncached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.BigintUncached.native.field83_0.source.value (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.originalProjection)] := member nonzero
  have present : Airbender.Compiler.LookupNative.BigintUncached.native.field83_0.source ∈ Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields ⟨205, by decide⟩
  have transported := Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintUncached.native.field83_0.source present
  have same := (Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.range_value22 physical data arithmetic).trans transported
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.BigintUncached.native.range16_clean_refinement _ valid _

theorem range_lookup23
    (sourceValue : Fin 276 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BigintUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BigintUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BigintUncached.native.assigned (Airbender.Compiler.HelperValidityNative.BigintUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BigintUncached.AuthoredLookupValid sourceValue) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression23).Contains (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BigintUncached.native.range16Queries.get ⟨23, by decide⟩
  have member := authored.2 query (List.get_mem Airbender.Compiler.LookupSourceNative.BigintUncached.native.range16Queries ⟨23, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.BigintUncached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.BigintUncached.native.field84_0.source.value (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.originalProjection)] := member nonzero
  have present : Airbender.Compiler.LookupNative.BigintUncached.native.field84_0.source ∈ Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields ⟨206, by decide⟩
  have transported := Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintUncached.native.field84_0.source present
  have same := (Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.range_value23 physical data arithmetic).trans transported
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.BigintUncached.native.range16_clean_refinement _ valid _

theorem range_lookup24
    (sourceValue : Fin 276 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BigintUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BigintUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BigintUncached.native.assigned (Airbender.Compiler.HelperValidityNative.BigintUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BigintUncached.AuthoredLookupValid sourceValue) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression24).Contains (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BigintUncached.native.range16Queries.get ⟨24, by decide⟩
  have member := authored.2 query (List.get_mem Airbender.Compiler.LookupSourceNative.BigintUncached.native.range16Queries ⟨24, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.BigintUncached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.BigintUncached.native.field85_0.source.value (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.originalProjection)] := member nonzero
  have present : Airbender.Compiler.LookupNative.BigintUncached.native.field85_0.source ∈ Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields ⟨207, by decide⟩
  have transported := Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintUncached.native.field85_0.source present
  have same := (Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.range_value24 physical data arithmetic).trans transported
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.BigintUncached.native.range16_clean_refinement _ valid _

theorem range_lookup25
    (sourceValue : Fin 276 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BigintUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BigintUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BigintUncached.native.assigned (Airbender.Compiler.HelperValidityNative.BigintUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BigintUncached.AuthoredLookupValid sourceValue) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression25).Contains (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BigintUncached.native.range16Queries.get ⟨25, by decide⟩
  have member := authored.2 query (List.get_mem Airbender.Compiler.LookupSourceNative.BigintUncached.native.range16Queries ⟨25, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.BigintUncached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.BigintUncached.native.field86_0.source.value (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.originalProjection)] := member nonzero
  have present : Airbender.Compiler.LookupNative.BigintUncached.native.field86_0.source ∈ Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields ⟨208, by decide⟩
  have transported := Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintUncached.native.field86_0.source present
  have same := (Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.range_value25 physical data arithmetic).trans transported
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.BigintUncached.native.range16_clean_refinement _ valid _

theorem range_lookup26
    (sourceValue : Fin 276 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BigintUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BigintUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BigintUncached.native.assigned (Airbender.Compiler.HelperValidityNative.BigintUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BigintUncached.AuthoredLookupValid sourceValue) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression26).Contains (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BigintUncached.native.range16Queries.get ⟨26, by decide⟩
  have member := authored.2 query (List.get_mem Airbender.Compiler.LookupSourceNative.BigintUncached.native.range16Queries ⟨26, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.BigintUncached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.BigintUncached.native.field87_0.source.value (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.originalProjection)] := member nonzero
  have present : Airbender.Compiler.LookupNative.BigintUncached.native.field87_0.source ∈ Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields ⟨209, by decide⟩
  have transported := Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintUncached.native.field87_0.source present
  have same := (Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.range_value26 physical data arithmetic).trans transported
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.BigintUncached.native.range16_clean_refinement _ valid _

theorem range_lookup27
    (sourceValue : Fin 276 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BigintUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BigintUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BigintUncached.native.assigned (Airbender.Compiler.HelperValidityNative.BigintUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BigintUncached.AuthoredLookupValid sourceValue) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression27).Contains (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BigintUncached.native.range16Queries.get ⟨27, by decide⟩
  have member := authored.2 query (List.get_mem Airbender.Compiler.LookupSourceNative.BigintUncached.native.range16Queries ⟨27, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.BigintUncached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.BigintUncached.native.field88_0.source.value (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.originalProjection)] := member nonzero
  have present : Airbender.Compiler.LookupNative.BigintUncached.native.field88_0.source ∈ Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields ⟨210, by decide⟩
  have transported := Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintUncached.native.field88_0.source present
  have same := (Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.range_value27 physical data arithmetic).trans transported
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.BigintUncached.native.range16_clean_refinement _ valid _

theorem range_lookup28
    (sourceValue : Fin 276 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BigintUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BigintUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BigintUncached.native.assigned (Airbender.Compiler.HelperValidityNative.BigintUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BigintUncached.AuthoredLookupValid sourceValue) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression28).Contains (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BigintUncached.native.range16Queries.get ⟨28, by decide⟩
  have member := authored.2 query (List.get_mem Airbender.Compiler.LookupSourceNative.BigintUncached.native.range16Queries ⟨28, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.BigintUncached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.BigintUncached.native.field89_0.source.value (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.originalProjection)] := member nonzero
  have present : Airbender.Compiler.LookupNative.BigintUncached.native.field89_0.source ∈ Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields ⟨211, by decide⟩
  have transported := Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintUncached.native.field89_0.source present
  have same := (Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.range_value28 physical data arithmetic).trans transported
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.BigintUncached.native.range16_clean_refinement _ valid _

theorem range_lookup29
    (sourceValue : Fin 276 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BigintUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BigintUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BigintUncached.native.assigned (Airbender.Compiler.HelperValidityNative.BigintUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BigintUncached.AuthoredLookupValid sourceValue) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression29).Contains (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BigintUncached.native.range16Queries.get ⟨29, by decide⟩
  have member := authored.2 query (List.get_mem Airbender.Compiler.LookupSourceNative.BigintUncached.native.range16Queries ⟨29, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.BigintUncached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.BigintUncached.native.field90_0.source.value (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.originalProjection)] := member nonzero
  have present : Airbender.Compiler.LookupNative.BigintUncached.native.field90_0.source ∈ Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields ⟨212, by decide⟩
  have transported := Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintUncached.native.field90_0.source present
  have same := (Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.range_value29 physical data arithmetic).trans transported
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.BigintUncached.native.range16_clean_refinement _ valid _

theorem range_lookup30
    (sourceValue : Fin 276 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BigintUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BigintUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BigintUncached.native.assigned (Airbender.Compiler.HelperValidityNative.BigintUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BigintUncached.AuthoredLookupValid sourceValue) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression30).Contains (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BigintUncached.native.range16Queries.get ⟨30, by decide⟩
  have member := authored.2 query (List.get_mem Airbender.Compiler.LookupSourceNative.BigintUncached.native.range16Queries ⟨30, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.BigintUncached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.BigintUncached.native.field91_0.source.value (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.originalProjection)] := member nonzero
  have present : Airbender.Compiler.LookupNative.BigintUncached.native.field91_0.source ∈ Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields ⟨213, by decide⟩
  have transported := Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintUncached.native.field91_0.source present
  have same := (Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.range_value30 physical data arithmetic).trans transported
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.BigintUncached.native.range16_clean_refinement _ valid _

theorem range_lookup31
    (sourceValue : Fin 276 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BigintUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BigintUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BigintUncached.native.assigned (Airbender.Compiler.HelperValidityNative.BigintUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BigintUncached.AuthoredLookupValid sourceValue) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression31).Contains (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BigintUncached.native.range16Queries.get ⟨31, by decide⟩
  have member := authored.2 query (List.get_mem Airbender.Compiler.LookupSourceNative.BigintUncached.native.range16Queries ⟨31, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.BigintUncached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.BigintUncached.native.field92_0.source.value (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.originalProjection)] := member nonzero
  have present : Airbender.Compiler.LookupNative.BigintUncached.native.field92_0.source ∈ Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields ⟨214, by decide⟩
  have transported := Airbender.Compiler.QueryFrameNative.BigintUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BigintUncached.native.field92_0.source present
  have same := (Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.range_value31 physical data arithmetic).trans transported
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.BigintUncached.native.range16_clean_refinement _ valid _

theorem retained_clock_from_source
    (sourceValue : Fin 276 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BigintUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BigintUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BigintUncached.native.assigned (Airbender.Compiler.HelperValidityNative.BigintUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank.address) = 0)
    (helpers : ∀ field ∈ Airbender.Compiler.HelperNative.BigintUncached.native.fields, (field.value (Airbender.Compiler.HelperNative.BigintUncached.native.sourceValues physical)).val < 524288)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BigintUncached.AuthoredLookupValid sourceValue) :
    FlatOperation.ConstraintsHoldFlat (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data) (Airbender.Bigint.clockConstraints (p := babyBearModulus) nativeSetup) := by
  apply Airbender.Compiler.CleanLinksNative.BigintUncached.retained_clock_constraints nativeSetup physical data arithmetic
  rw [clock_lookup_inventory]
  exact PredicateChecks.all (PredicateChecks.cons (range_lookup0 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (range_lookup1 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (range_lookup2 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (range_lookup3 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (range_lookup4 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (range_lookup5 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (range_lookup6 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (range_lookup7 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (range_lookup8 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (range_lookup9 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (range_lookup10 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (range_lookup11 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (range_lookup12 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (range_lookup13 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (range_lookup14 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (range_lookup15 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (range_lookup16 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (range_lookup17 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (range_lookup18 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (range_lookup19 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (range_lookup20 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (range_lookup21 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (range_lookup22 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (range_lookup23 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (range_lookup24 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (range_lookup25 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (range_lookup26 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (range_lookup27 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (range_lookup28 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (range_lookup29 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (range_lookup30 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (range_lookup31 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression39 (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestamp_bound39 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression40 (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestamp_bound40 physical data arithmetic helpers)) (PredicateChecks.cons (generic_lookup0 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (generic_lookup1 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (generic_lookup2 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (generic_lookup3 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (generic_lookup4 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (generic_lookup5 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (generic_lookup6 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (generic_lookup7 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (generic_lookup8 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (generic_lookup9 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (generic_lookup10 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (generic_lookup11 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (generic_lookup12 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (generic_lookup13 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (generic_lookup14 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (generic_lookup15 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (generic_lookup16 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (generic_lookup17 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (generic_lookup18 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (generic_lookup19 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (generic_lookup20 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (generic_lookup21 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (generic_lookup22 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (generic_lookup23 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (generic_lookup24 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (generic_lookup25 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (generic_lookup26 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (generic_lookup27 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (generic_lookup28 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (generic_lookup29 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (generic_lookup30 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (generic_lookup31 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (generic_lookup32 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (generic_lookup33 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (generic_lookup34 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (generic_lookup35 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (generic_lookup36 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (generic_lookup37 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (generic_lookup38 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (generic_lookup39 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (generic_lookup40 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (generic_lookup41 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (generic_lookup42 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (generic_lookup43 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (generic_lookup44 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (generic_lookup45 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (generic_lookup46 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (generic_lookup47 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (generic_lookup48 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (generic_lookup49 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (generic_lookup50 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (generic_lookup51 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (generic_lookup52 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (generic_lookup53 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (generic_lookup54 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (generic_lookup55 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (generic_lookup56 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (generic_lookup57 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (generic_lookup58 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (generic_lookup59 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (generic_lookup60 sourceValue counts physical data inputAgreement arithmetic authored) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression0 (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestamp_bound0 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression1 (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestamp_bound1 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression2 (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestamp_bound2 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression3 (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestamp_bound3 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression4 (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestamp_bound4 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression5 (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestamp_bound5 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression6 (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestamp_bound6 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression7 (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestamp_bound7 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression8 (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestamp_bound8 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression9 (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestamp_bound9 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression10 (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestamp_bound10 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression11 (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestamp_bound11 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression12 (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestamp_bound12 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression13 (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestamp_bound13 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression14 (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestamp_bound14 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression15 (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestamp_bound15 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression16 (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestamp_bound16 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression17 (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestamp_bound17 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression18 (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestamp_bound18 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression19 (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestamp_bound19 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression20 (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestamp_bound20 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression21 (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestamp_bound21 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression22 (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestamp_bound22 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression23 (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestamp_bound23 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression24 (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestamp_bound24 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression25 (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestamp_bound25 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression26 (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestamp_bound26 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression27 (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestamp_bound27 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression28 (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestamp_bound28 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression29 (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestamp_bound29 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression30 (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestamp_bound30 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression31 (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestamp_bound31 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression32 (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestamp_bound32 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression33 (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestamp_bound33 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression34 (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestamp_bound34 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression35 (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestamp_bound35 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression36 (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestamp_bound36 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression37 (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestamp_bound37 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression38 (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestamp_bound38 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression39 (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestamp_bound39 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression40 (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestamp_bound40 physical data arithmetic helpers)) PredicateChecks.nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

end Airbender.Compiler.CleanClosedNative.BigintUncached
