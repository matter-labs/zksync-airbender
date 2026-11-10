import Airbender.Import.GKRProtocol.OracleFrameImport
import Airbender.Proofs.GKRProtocol.CounterFrameNative.UnifiedCached
import Airbender.Proofs.GKRProtocol.MaterializedNative.UnifiedCached

namespace Airbender.Compiler.OracleFrameNative.UnifiedCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_lookup_oracle_frame native from "artifacts/compiler/unified-cached.json"
  base_model Airbender.Compiler.FullArithmeticNative.UnifiedCached.native typing Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing

theorem oracle_graph_extends {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (sourceValue : Fin 137 → Source.BaseField)
    (original : Satisfies (Airbender.Compiler.SourceContractNative.UnifiedCached.native.originals.map Expression.polynomial) sourceValue)
    (clockValid : Source.clockContract Airbender.Compiler.SourceContractNative.UnifiedCached.native.clock (Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.helperPlacement.memory.project sourceValue))
    (primitives : Airbender.Compiler.HelperValidityNative.UnifiedCached.native.profile.ExecutionValid (Airbender.Compiler.HelperValidityNative.UnifiedCached.native.execute.value (Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.helperPlacement.memory.project sourceValue))
      (Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.helperPlacement.memory.project sourceValue))
    (counts : Fin Airbender.Compiler.TableNative.UnifiedCached.native.multiplicityColumns.length → Source.BaseField)
    (row : Fin Airbender.Compiler.MaterializedNative.UnifiedCached.native.model.imported.data.length) (fallback : GKRAddress → Source.BaseField) :
    ∃ baseValue : GKRAddress → Source.BaseField, ∃ values : GKRAddress → R,
      (∀ wire, baseValue (Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.UnifiedCached.native.assigned (Airbender.Compiler.HelperValidityNative.UnifiedCached.native.canonical sourceValue) counts wire) ∧
      (∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (baseValue ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0) ∧
      (∀ address, Airbender.Compiler.FunctionalNative.UnifiedCached.native.isBase address = true → values address = hom (baseValue address)) ∧
      (∀ definition ∈ Airbender.Compiler.FunctionalNative.UnifiedCached.native.definitions, definition.Holds hom challenges values) ∧
      (∀ gate ∈ Airbender.Compiler.LookupNative.UnifiedCached.native.gates, gate.Holds hom challenges gamma values) ∧
      (∀ gate ∈ Airbender.Compiler.ProductNative.UnifiedCached.native.gates, gate.Holds hom challenges values) ∧
      (∀ index, baseValue (GKRAddress.BaseLayerWitness (Airbender.Compiler.TableNative.UnifiedCached.native.multiplicityColumns.get index)) = counts index) ∧
      (∀ column ∈ native.columns, baseValue column.address = Airbender.Compiler.MaterializedNative.UnifiedCached.native.model.value row column) ∧
      (∀ field ∈ Airbender.Compiler.HelperNative.UnifiedCached.native.fields, (field.value (Airbender.Compiler.HelperNative.UnifiedCached.native.sourceValues baseValue)).val < 524288) := by
  let initial := Airbender.Compiler.HelperValidityNative.UnifiedCached.native.canonical sourceValue
  let extended := Airbender.Compiler.CounterFrameNative.UnifiedCached.native.assigned initial counts
  have holds := Airbender.Compiler.CounterFrameNative.UnifiedCached.native.source_preserved initial counts (Airbender.Compiler.HelperValidityNative.UnifiedCached.native.source_holds sourceValue original clockValid)
  let full := Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.translation.extend extended
  let baseValue := Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.materialize full (Airbender.Compiler.MaterializedNative.UnifiedCached.native.model.baseOracle row fallback)
  have arithmetic := Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.full_arithmetic_extends extended holds
  have baseArithmetic := WireBank.materialize_gates Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bankRoundTrip full
    (Airbender.Compiler.MaterializedNative.UnifiedCached.native.model.baseOracle row fallback) Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates arithmetic.2
  have inputAgreement (wire) : baseValue (Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.inputBank.address wire) = extended wire :=
    WireBank.materialize_source_input Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.inputBank Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.projection
      Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.inputCoordinates Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bankRoundTrip extended full arithmetic.1
      (Airbender.Compiler.MaterializedNative.UnifiedCached.native.model.baseOracle row fallback) wire
  refine ⟨baseValue, Airbender.Compiler.FunctionalNative.UnifiedCached.native.canonical hom challenges gamma baseValue, inputAgreement, baseArithmetic,
    Airbender.Compiler.FunctionalNative.UnifiedCached.native.canonical_base hom challenges gamma baseValue,
    Airbender.Compiler.FunctionalNative.UnifiedCached.native.canonical_affines hom challenges gamma baseValue baseArithmetic,
    Airbender.Compiler.FunctionalNative.UnifiedCached.native.canonical_lookups hom challenges gamma baseValue,
    Airbender.Compiler.FunctionalNative.UnifiedCached.native.canonical_products hom challenges gamma baseValue, ?_,
    native.materialized_cells Airbender.Compiler.MaterializedNative.UnifiedCached.native.model row fallback full, ?_⟩
  · intro index
    have actual := inputAgreement (Airbender.Compiler.CounterFrameNative.UnifiedCached.native.slots index)
    rw [Airbender.Compiler.CounterFrameNative.UnifiedCached.native.slotsRoundTrip index] at actual
    exact actual.trans (Airbender.Compiler.CounterFrameNative.UnifiedCached.native.counts_at initial counts index)
  · intro field member
    have same := Source.HelperField.transport_value field Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.helperPlacement Airbender.Compiler.HelperNative.UnifiedCached.native.placement
      Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.inputBank Airbender.Compiler.MemoryNative.UnifiedCached.native.bank (List.all_eq_true.mp Airbender.Compiler.HelperValidityNative.UnifiedCached.native.transportChecked field member)
      extended baseValue inputAgreement
    change (field.value (Airbender.Compiler.HelperNative.UnifiedCached.native.placement.project (baseValue ∘ Airbender.Compiler.MemoryNative.UnifiedCached.native.bank.address))).val < 524288
    rw [same, Airbender.Compiler.CounterFrameNative.UnifiedCached.native.helpers_preserved initial counts field member]
    exact Airbender.Compiler.HelperValidityNative.UnifiedCached.native.helper_membership sourceValue primitives field member

end Airbender.Compiler.OracleFrameNative.UnifiedCached
