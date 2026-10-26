import Airbender.Import.GKRProtocol.OracleFrameImport
import Airbender.Proofs.GKRProtocol.CounterFrameNative.WordMemoryUncached
import Airbender.Proofs.GKRProtocol.MaterializedNative.WordMemoryUncached

namespace Airbender.Compiler.OracleFrameNative.WordMemoryUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_lookup_oracle_frame native from "artifacts/compiler/word-memory-uncached.json"
  base_model Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native typing Airbender.Compiler.ConsumerNative.WordMemoryUncached.native.typing

theorem oracle_graph_extends {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (sourceValue : Fin 52 → Source.BaseField)
    (original : Satisfies (Airbender.Compiler.SourceContractNative.WordMemoryUncached.native.originals.map Expression.polynomial) sourceValue)
    (clockValid : Source.clockContract Airbender.Compiler.SourceContractNative.WordMemoryUncached.native.clock (Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.helperPlacement.memory.project sourceValue))
    (primitives : Airbender.Compiler.HelperValidityNative.WordMemoryUncached.native.profile.ExecutionValid (Airbender.Compiler.HelperValidityNative.WordMemoryUncached.native.execute.value (Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.helperPlacement.memory.project sourceValue))
      (Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.helperPlacement.memory.project sourceValue))
    (counts : Fin Airbender.Compiler.TableNative.WordMemoryUncached.native.multiplicityColumns.length → Source.BaseField)
    (row : Fin Airbender.Compiler.MaterializedNative.WordMemoryUncached.native.model.imported.data.length) (fallback : GKRAddress → Source.BaseField) :
    ∃ baseValue : GKRAddress → Source.BaseField, ∃ values : GKRAddress → R,
      (∀ wire, baseValue (Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.WordMemoryUncached.native.assigned (Airbender.Compiler.HelperValidityNative.WordMemoryUncached.native.canonical sourceValue) counts wire) ∧
      (∀ gate ∈ Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.artifact.gates, gate.expressionResidual (baseValue ∘ Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.bank.address) = 0) ∧
      (∀ address, Airbender.Compiler.FunctionalNative.WordMemoryUncached.native.isBase address = true → values address = hom (baseValue address)) ∧
      (∀ definition ∈ Airbender.Compiler.FunctionalNative.WordMemoryUncached.native.definitions, definition.Holds hom challenges values) ∧
      (∀ gate ∈ Airbender.Compiler.LookupNative.WordMemoryUncached.native.gates, gate.Holds hom challenges gamma values) ∧
      (∀ gate ∈ Airbender.Compiler.ProductNative.WordMemoryUncached.native.gates, gate.Holds hom challenges values) ∧
      (∀ index, baseValue (GKRAddress.BaseLayerWitness (Airbender.Compiler.TableNative.WordMemoryUncached.native.multiplicityColumns.get index)) = counts index) ∧
      (∀ column ∈ native.columns, baseValue column.address = Airbender.Compiler.MaterializedNative.WordMemoryUncached.native.model.value row column) ∧
      (∀ field ∈ Airbender.Compiler.HelperNative.WordMemoryUncached.native.fields, (field.value (Airbender.Compiler.HelperNative.WordMemoryUncached.native.sourceValues baseValue)).val < 524288) := by
  let initial := Airbender.Compiler.HelperValidityNative.WordMemoryUncached.native.canonical sourceValue
  let extended := Airbender.Compiler.CounterFrameNative.WordMemoryUncached.native.assigned initial counts
  have holds := Airbender.Compiler.CounterFrameNative.WordMemoryUncached.native.source_preserved initial counts (Airbender.Compiler.HelperValidityNative.WordMemoryUncached.native.source_holds sourceValue original clockValid)
  let full := Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.artifact.translation.extend extended
  let baseValue := Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.bank.materialize full (Airbender.Compiler.MaterializedNative.WordMemoryUncached.native.model.baseOracle row fallback)
  have arithmetic := Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.full_arithmetic_extends extended holds
  have baseArithmetic := WireBank.materialize_gates Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.bank Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.bankRoundTrip full
    (Airbender.Compiler.MaterializedNative.WordMemoryUncached.native.model.baseOracle row fallback) Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.artifact.gates arithmetic.2
  have inputAgreement (wire) : baseValue (Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.inputBank.address wire) = extended wire :=
    WireBank.materialize_source_input Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.bank Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.inputBank Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.artifact.projection
      Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.inputCoordinates Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.bankRoundTrip extended full arithmetic.1
      (Airbender.Compiler.MaterializedNative.WordMemoryUncached.native.model.baseOracle row fallback) wire
  refine ⟨baseValue, Airbender.Compiler.FunctionalNative.WordMemoryUncached.native.canonical hom challenges gamma baseValue, inputAgreement, baseArithmetic,
    Airbender.Compiler.FunctionalNative.WordMemoryUncached.native.canonical_base hom challenges gamma baseValue,
    Airbender.Compiler.FunctionalNative.WordMemoryUncached.native.canonical_affines hom challenges gamma baseValue baseArithmetic,
    Airbender.Compiler.FunctionalNative.WordMemoryUncached.native.canonical_lookups hom challenges gamma baseValue,
    Airbender.Compiler.FunctionalNative.WordMemoryUncached.native.canonical_products hom challenges gamma baseValue, ?_,
    native.materialized_cells Airbender.Compiler.MaterializedNative.WordMemoryUncached.native.model row fallback full, ?_⟩
  · intro index
    have actual := inputAgreement (Airbender.Compiler.CounterFrameNative.WordMemoryUncached.native.slots index)
    rw [Airbender.Compiler.CounterFrameNative.WordMemoryUncached.native.slotsRoundTrip index] at actual
    exact actual.trans (Airbender.Compiler.CounterFrameNative.WordMemoryUncached.native.counts_at initial counts index)
  · intro field member
    have same := Source.HelperField.transport_value field Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.helperPlacement Airbender.Compiler.HelperNative.WordMemoryUncached.native.placement
      Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.inputBank Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank (List.all_eq_true.mp Airbender.Compiler.HelperValidityNative.WordMemoryUncached.native.transportChecked field member)
      extended baseValue inputAgreement
    change (field.value (Airbender.Compiler.HelperNative.WordMemoryUncached.native.placement.project (baseValue ∘ Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank.address))).val < 524288
    rw [same, Airbender.Compiler.CounterFrameNative.WordMemoryUncached.native.helpers_preserved initial counts field member]
    exact Airbender.Compiler.HelperValidityNative.WordMemoryUncached.native.helper_membership sourceValue primitives field member

end Airbender.Compiler.OracleFrameNative.WordMemoryUncached
