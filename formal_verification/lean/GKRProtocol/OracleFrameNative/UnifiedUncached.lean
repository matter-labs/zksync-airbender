import GKRProtocol.OracleFrameImport
import GKRProtocol.CounterFrameNative.UnifiedUncached
import GKRProtocol.MaterializedNative.UnifiedUncached

namespace Airbender.Compiler.OracleFrameNative.UnifiedUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_lookup_oracle_frame native from "artifacts/compiler/unified-uncached.json"
  base_model Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native typing Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing

theorem oracle_graph_extends {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (sourceValue : Fin 145 → Source.BaseField)
    (original : Satisfies (Airbender.Compiler.SourceContractNative.UnifiedUncached.native.originals.map Expression.polynomial) sourceValue)
    (clockValid : Source.clockContract Airbender.Compiler.SourceContractNative.UnifiedUncached.native.clock (Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.helperPlacement.memory.project sourceValue))
    (primitives : Airbender.Compiler.HelperValidityNative.UnifiedUncached.native.profile.ExecutionValid (Airbender.Compiler.HelperValidityNative.UnifiedUncached.native.execute.value (Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.helperPlacement.memory.project sourceValue))
      (Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.helperPlacement.memory.project sourceValue))
    (counts : Fin Airbender.Compiler.TableNative.UnifiedUncached.native.multiplicityColumns.length → Source.BaseField)
    (row : Fin Airbender.Compiler.MaterializedNative.UnifiedUncached.native.model.imported.data.length) (fallback : GKRAddress → Source.BaseField) :
    ∃ baseValue : GKRAddress → Source.BaseField, ∃ values : GKRAddress → R,
      (∀ wire, baseValue (Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.UnifiedUncached.native.assigned (Airbender.Compiler.HelperValidityNative.UnifiedUncached.native.canonical sourceValue) counts wire) ∧
      (∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.artifact.gates, gate.expressionResidual (baseValue ∘ Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.bank.address) = 0) ∧
      (∀ address, Airbender.Compiler.FunctionalNative.UnifiedUncached.native.isBase address = true → values address = hom (baseValue address)) ∧
      (∀ definition ∈ Airbender.Compiler.FunctionalNative.UnifiedUncached.native.definitions, definition.Holds hom challenges values) ∧
      (∀ gate ∈ Airbender.Compiler.LookupNative.UnifiedUncached.native.gates, gate.Holds hom challenges gamma values) ∧
      (∀ gate ∈ Airbender.Compiler.ProductNative.UnifiedUncached.native.gates, gate.Holds hom challenges values) ∧
      (∀ index, baseValue (GKRAddress.BaseLayerWitness (Airbender.Compiler.TableNative.UnifiedUncached.native.multiplicityColumns.get index)) = counts index) ∧
      (∀ column ∈ native.columns, baseValue column.address = Airbender.Compiler.MaterializedNative.UnifiedUncached.native.model.value row column) ∧
      (∀ field ∈ Airbender.Compiler.HelperNative.UnifiedUncached.native.fields, (field.value (Airbender.Compiler.HelperNative.UnifiedUncached.native.sourceValues baseValue)).val < 524288) := by
  let initial := Airbender.Compiler.HelperValidityNative.UnifiedUncached.native.canonical sourceValue
  let extended := Airbender.Compiler.CounterFrameNative.UnifiedUncached.native.assigned initial counts
  have holds := Airbender.Compiler.CounterFrameNative.UnifiedUncached.native.source_preserved initial counts (Airbender.Compiler.HelperValidityNative.UnifiedUncached.native.source_holds sourceValue original clockValid)
  let full := Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.artifact.translation.extend extended
  let baseValue := Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.bank.materialize full (Airbender.Compiler.MaterializedNative.UnifiedUncached.native.model.baseOracle row fallback)
  have arithmetic := Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.full_arithmetic_extends extended holds
  have baseArithmetic := WireBank.materialize_gates Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.bank Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.bankRoundTrip full
    (Airbender.Compiler.MaterializedNative.UnifiedUncached.native.model.baseOracle row fallback) Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.artifact.gates arithmetic.2
  have inputAgreement (wire) : baseValue (Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.inputBank.address wire) = extended wire :=
    WireBank.materialize_source_input Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.bank Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.inputBank Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.artifact.projection
      Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.inputCoordinates Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.bankRoundTrip extended full arithmetic.1
      (Airbender.Compiler.MaterializedNative.UnifiedUncached.native.model.baseOracle row fallback) wire
  refine ⟨baseValue, Airbender.Compiler.FunctionalNative.UnifiedUncached.native.canonical hom challenges gamma baseValue, inputAgreement, baseArithmetic,
    Airbender.Compiler.FunctionalNative.UnifiedUncached.native.canonical_base hom challenges gamma baseValue,
    Airbender.Compiler.FunctionalNative.UnifiedUncached.native.canonical_affines hom challenges gamma baseValue baseArithmetic,
    Airbender.Compiler.FunctionalNative.UnifiedUncached.native.canonical_lookups hom challenges gamma baseValue,
    Airbender.Compiler.FunctionalNative.UnifiedUncached.native.canonical_products hom challenges gamma baseValue, ?_,
    native.materialized_cells Airbender.Compiler.MaterializedNative.UnifiedUncached.native.model row fallback full, ?_⟩
  · intro index
    have actual := inputAgreement (Airbender.Compiler.CounterFrameNative.UnifiedUncached.native.slots index)
    rw [Airbender.Compiler.CounterFrameNative.UnifiedUncached.native.slotsRoundTrip index] at actual
    exact actual.trans (Airbender.Compiler.CounterFrameNative.UnifiedUncached.native.counts_at initial counts index)
  · intro field member
    have same := Source.HelperField.transport_value field Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.helperPlacement Airbender.Compiler.HelperNative.UnifiedUncached.native.placement
      Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.inputBank Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank (List.all_eq_true.mp Airbender.Compiler.HelperValidityNative.UnifiedUncached.native.transportChecked field member)
      extended baseValue inputAgreement
    change (field.value (Airbender.Compiler.HelperNative.UnifiedUncached.native.placement.project (baseValue ∘ Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank.address))).val < 524288
    rw [same, Airbender.Compiler.CounterFrameNative.UnifiedUncached.native.helpers_preserved initial counts field member]
    exact Airbender.Compiler.HelperValidityNative.UnifiedUncached.native.helper_membership sourceValue primitives field member

end Airbender.Compiler.OracleFrameNative.UnifiedUncached
