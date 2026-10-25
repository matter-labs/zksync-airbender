import GKRProtocol.OracleFrameImport
import GKRProtocol.CounterFrameNative.BlakeGUncached
import GKRProtocol.MaterializedNative.BlakeGUncached

namespace Airbender.Compiler.OracleFrameNative.BlakeGUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_lookup_oracle_frame native from "artifacts/compiler/blake-g-uncached.json"
  base_model Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native typing Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing

theorem oracle_graph_extends {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (sourceValue : Fin 113 → Source.BaseField)
    (original : Satisfies (Airbender.Compiler.SourceContractNative.BlakeGUncached.native.originals.map Expression.polynomial) sourceValue)
    (clockValid : Source.clockContract Airbender.Compiler.SourceContractNative.BlakeGUncached.native.clock (Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.helperPlacement.memory.project sourceValue))
    (primitives : Airbender.Compiler.HelperValidityNative.BlakeGUncached.native.profile.ExecutionValid (Airbender.Compiler.HelperValidityNative.BlakeGUncached.native.execute.value (Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.helperPlacement.memory.project sourceValue))
      (Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.helperPlacement.memory.project sourceValue))
    (counts : Fin Airbender.Compiler.TableNative.BlakeGUncached.native.multiplicityColumns.length → Source.BaseField)
    (row : Fin Airbender.Compiler.MaterializedNative.BlakeGUncached.native.model.imported.data.length) (fallback : GKRAddress → Source.BaseField) :
    ∃ baseValue : GKRAddress → Source.BaseField, ∃ values : GKRAddress → R,
      (∀ wire, baseValue (Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BlakeGUncached.native.assigned (Airbender.Compiler.HelperValidityNative.BlakeGUncached.native.canonical sourceValue) counts wire) ∧
      (∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.artifact.gates, gate.expressionResidual (baseValue ∘ Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.bank.address) = 0) ∧
      (∀ address, Airbender.Compiler.FunctionalNative.BlakeGUncached.native.isBase address = true → values address = hom (baseValue address)) ∧
      (∀ definition ∈ Airbender.Compiler.FunctionalNative.BlakeGUncached.native.definitions, definition.Holds hom challenges values) ∧
      (∀ gate ∈ Airbender.Compiler.LookupNative.BlakeGUncached.native.gates, gate.Holds hom challenges gamma values) ∧
      (∀ gate ∈ Airbender.Compiler.ProductNative.BlakeGUncached.native.gates, gate.Holds hom challenges values) ∧
      (∀ index, baseValue (GKRAddress.BaseLayerWitness (Airbender.Compiler.TableNative.BlakeGUncached.native.multiplicityColumns.get index)) = counts index) ∧
      (∀ column ∈ native.columns, baseValue column.address = Airbender.Compiler.MaterializedNative.BlakeGUncached.native.model.value row column) ∧
      (∀ field ∈ Airbender.Compiler.HelperNative.BlakeGUncached.native.fields, (field.value (Airbender.Compiler.HelperNative.BlakeGUncached.native.sourceValues baseValue)).val < 524288) := by
  let initial := Airbender.Compiler.HelperValidityNative.BlakeGUncached.native.canonical sourceValue
  let extended := Airbender.Compiler.CounterFrameNative.BlakeGUncached.native.assigned initial counts
  have holds := Airbender.Compiler.CounterFrameNative.BlakeGUncached.native.source_preserved initial counts (Airbender.Compiler.HelperValidityNative.BlakeGUncached.native.source_holds sourceValue original clockValid)
  let full := Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.artifact.translation.extend extended
  let baseValue := Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.bank.materialize full (Airbender.Compiler.MaterializedNative.BlakeGUncached.native.model.baseOracle row fallback)
  have arithmetic := Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.full_arithmetic_extends extended holds
  have baseArithmetic := WireBank.materialize_gates Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.bank Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.bankRoundTrip full
    (Airbender.Compiler.MaterializedNative.BlakeGUncached.native.model.baseOracle row fallback) Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.artifact.gates arithmetic.2
  have inputAgreement (wire) : baseValue (Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.inputBank.address wire) = extended wire :=
    WireBank.materialize_source_input Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.bank Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.inputBank Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.artifact.projection
      Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.inputCoordinates Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.bankRoundTrip extended full arithmetic.1
      (Airbender.Compiler.MaterializedNative.BlakeGUncached.native.model.baseOracle row fallback) wire
  refine ⟨baseValue, Airbender.Compiler.FunctionalNative.BlakeGUncached.native.canonical hom challenges gamma baseValue, inputAgreement, baseArithmetic,
    Airbender.Compiler.FunctionalNative.BlakeGUncached.native.canonical_base hom challenges gamma baseValue,
    Airbender.Compiler.FunctionalNative.BlakeGUncached.native.canonical_affines hom challenges gamma baseValue baseArithmetic,
    Airbender.Compiler.FunctionalNative.BlakeGUncached.native.canonical_lookups hom challenges gamma baseValue,
    Airbender.Compiler.FunctionalNative.BlakeGUncached.native.canonical_products hom challenges gamma baseValue, ?_,
    native.materialized_cells Airbender.Compiler.MaterializedNative.BlakeGUncached.native.model row fallback full, ?_⟩
  · intro index
    have actual := inputAgreement (Airbender.Compiler.CounterFrameNative.BlakeGUncached.native.slots index)
    rw [Airbender.Compiler.CounterFrameNative.BlakeGUncached.native.slotsRoundTrip index] at actual
    exact actual.trans (Airbender.Compiler.CounterFrameNative.BlakeGUncached.native.counts_at initial counts index)
  · intro field member
    have same := Source.HelperField.transport_value field Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.helperPlacement Airbender.Compiler.HelperNative.BlakeGUncached.native.placement
      Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.inputBank Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank (List.all_eq_true.mp Airbender.Compiler.HelperValidityNative.BlakeGUncached.native.transportChecked field member)
      extended baseValue inputAgreement
    change (field.value (Airbender.Compiler.HelperNative.BlakeGUncached.native.placement.project (baseValue ∘ Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank.address))).val < 524288
    rw [same, Airbender.Compiler.CounterFrameNative.BlakeGUncached.native.helpers_preserved initial counts field member]
    exact Airbender.Compiler.HelperValidityNative.BlakeGUncached.native.helper_membership sourceValue primitives field member

end Airbender.Compiler.OracleFrameNative.BlakeGUncached
