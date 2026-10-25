import GKRProtocol.OracleFrameImport
import GKRProtocol.CounterFrameNative.BlakeRoundCached
import GKRProtocol.MaterializedNative.BlakeRoundCached

namespace Airbender.Compiler.OracleFrameNative.BlakeRoundCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_lookup_oracle_frame native from "artifacts/compiler/blake-round-cached.json"
  base_model Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native typing Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing

theorem oracle_graph_extends {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (sourceValue : Fin 763 → Source.BaseField)
    (original : Satisfies (Airbender.Compiler.SourceContractNative.BlakeRoundCached.native.originals.map Expression.polynomial) sourceValue)
    (clockValid : Source.clockContract Airbender.Compiler.SourceContractNative.BlakeRoundCached.native.clock (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.helperPlacement.memory.project sourceValue))
    (primitives : Airbender.Compiler.HelperValidityNative.BlakeRoundCached.native.profile.ExecutionValid (Airbender.Compiler.HelperValidityNative.BlakeRoundCached.native.execute.value (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.helperPlacement.memory.project sourceValue))
      (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.helperPlacement.memory.project sourceValue))
    (counts : Fin Airbender.Compiler.TableNative.BlakeRoundCached.native.multiplicityColumns.length → Source.BaseField)
    (row : Fin Airbender.Compiler.MaterializedNative.BlakeRoundCached.native.model.imported.data.length) (fallback : GKRAddress → Source.BaseField) :
    ∃ baseValue : GKRAddress → Source.BaseField, ∃ values : GKRAddress → R,
      (∀ wire, baseValue (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BlakeRoundCached.native.assigned (Airbender.Compiler.HelperValidityNative.BlakeRoundCached.native.canonical sourceValue) counts wire) ∧
      (∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.artifact.gates, gate.expressionResidual (baseValue ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0) ∧
      (∀ address, Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.isBase address = true → values address = hom (baseValue address)) ∧
      (∀ definition ∈ Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.definitions, definition.Holds hom challenges values) ∧
      (∀ gate ∈ Airbender.Compiler.LookupNative.BlakeRoundCached.native.gates, gate.Holds hom challenges gamma values) ∧
      (∀ gate ∈ Airbender.Compiler.ProductNative.BlakeRoundCached.native.gates, gate.Holds hom challenges values) ∧
      (∀ index, baseValue (GKRAddress.BaseLayerWitness (Airbender.Compiler.TableNative.BlakeRoundCached.native.multiplicityColumns.get index)) = counts index) ∧
      (∀ column ∈ native.columns, baseValue column.address = Airbender.Compiler.MaterializedNative.BlakeRoundCached.native.model.value row column) ∧
      (∀ field ∈ Airbender.Compiler.HelperNative.BlakeRoundCached.native.fields, (field.value (Airbender.Compiler.HelperNative.BlakeRoundCached.native.sourceValues baseValue)).val < 524288) := by
  let initial := Airbender.Compiler.HelperValidityNative.BlakeRoundCached.native.canonical sourceValue
  let extended := Airbender.Compiler.CounterFrameNative.BlakeRoundCached.native.assigned initial counts
  have holds := Airbender.Compiler.CounterFrameNative.BlakeRoundCached.native.source_preserved initial counts (Airbender.Compiler.HelperValidityNative.BlakeRoundCached.native.source_holds sourceValue original clockValid)
  let full := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.artifact.translation.extend extended
  let baseValue := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.materialize full (Airbender.Compiler.MaterializedNative.BlakeRoundCached.native.model.baseOracle row fallback)
  have arithmetic := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.full_arithmetic_extends extended holds
  have baseArithmetic := WireBank.materialize_gates Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bankRoundTrip full
    (Airbender.Compiler.MaterializedNative.BlakeRoundCached.native.model.baseOracle row fallback) Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.artifact.gates arithmetic.2
  have inputAgreement (wire) : baseValue (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.inputBank.address wire) = extended wire :=
    WireBank.materialize_source_input Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.inputBank Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.artifact.projection
      Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.inputCoordinates Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bankRoundTrip extended full arithmetic.1
      (Airbender.Compiler.MaterializedNative.BlakeRoundCached.native.model.baseOracle row fallback) wire
  refine ⟨baseValue, Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.canonical hom challenges gamma baseValue, inputAgreement, baseArithmetic,
    Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.canonical_base hom challenges gamma baseValue,
    Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.canonical_affines hom challenges gamma baseValue baseArithmetic,
    Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.canonical_lookups hom challenges gamma baseValue,
    Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.canonical_products hom challenges gamma baseValue, ?_,
    native.materialized_cells Airbender.Compiler.MaterializedNative.BlakeRoundCached.native.model row fallback full, ?_⟩
  · intro index
    have actual := inputAgreement (Airbender.Compiler.CounterFrameNative.BlakeRoundCached.native.slots index)
    rw [Airbender.Compiler.CounterFrameNative.BlakeRoundCached.native.slotsRoundTrip index] at actual
    exact actual.trans (Airbender.Compiler.CounterFrameNative.BlakeRoundCached.native.counts_at initial counts index)
  · intro field member
    have same := Source.HelperField.transport_value field Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.helperPlacement Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement
      Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.inputBank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank (List.all_eq_true.mp Airbender.Compiler.HelperValidityNative.BlakeRoundCached.native.transportChecked field member)
      extended baseValue inputAgreement
    change (field.value (Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement.project (baseValue ∘ Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank.address))).val < 524288
    rw [same, Airbender.Compiler.CounterFrameNative.BlakeRoundCached.native.helpers_preserved initial counts field member]
    exact Airbender.Compiler.HelperValidityNative.BlakeRoundCached.native.helper_membership sourceValue primitives field member

end Airbender.Compiler.OracleFrameNative.BlakeRoundCached
