import GKRProtocol.OracleFrameImport
import GKRProtocol.CounterFrameNative.SubwordMemoryCached
import GKRProtocol.MaterializedNative.SubwordMemoryCached

namespace Airbender.Compiler.OracleFrameNative.SubwordMemoryCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_lookup_oracle_frame native from "artifacts/compiler/subword-memory-cached.json"
  base_model Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native typing Airbender.Compiler.ConsumerNative.SubwordMemoryCached.native.typing

theorem oracle_graph_extends {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (sourceValue : Fin 68 → Source.BaseField)
    (original : Satisfies (Airbender.Compiler.SourceContractNative.SubwordMemoryCached.native.originals.map Expression.polynomial) sourceValue)
    (clockValid : Source.clockContract Airbender.Compiler.SourceContractNative.SubwordMemoryCached.native.clock (Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.helperPlacement.memory.project sourceValue))
    (primitives : Airbender.Compiler.HelperValidityNative.SubwordMemoryCached.native.profile.ExecutionValid (Airbender.Compiler.HelperValidityNative.SubwordMemoryCached.native.execute.value (Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.helperPlacement.memory.project sourceValue))
      (Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.helperPlacement.memory.project sourceValue))
    (counts : Fin Airbender.Compiler.TableNative.SubwordMemoryCached.native.multiplicityColumns.length → Source.BaseField)
    (row : Fin Airbender.Compiler.MaterializedNative.SubwordMemoryCached.native.model.imported.data.length) (fallback : GKRAddress → Source.BaseField) :
    ∃ baseValue : GKRAddress → Source.BaseField, ∃ values : GKRAddress → R,
      (∀ wire, baseValue (Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.SubwordMemoryCached.native.assigned (Airbender.Compiler.HelperValidityNative.SubwordMemoryCached.native.canonical sourceValue) counts wire) ∧
      (∀ gate ∈ Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.artifact.gates, gate.expressionResidual (baseValue ∘ Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.bank.address) = 0) ∧
      (∀ address, Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.isBase address = true → values address = hom (baseValue address)) ∧
      (∀ definition ∈ Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.definitions, definition.Holds hom challenges values) ∧
      (∀ gate ∈ Airbender.Compiler.LookupNative.SubwordMemoryCached.native.gates, gate.Holds hom challenges gamma values) ∧
      (∀ gate ∈ Airbender.Compiler.ProductNative.SubwordMemoryCached.native.gates, gate.Holds hom challenges values) ∧
      (∀ index, baseValue (GKRAddress.BaseLayerWitness (Airbender.Compiler.TableNative.SubwordMemoryCached.native.multiplicityColumns.get index)) = counts index) ∧
      (∀ column ∈ native.columns, baseValue column.address = Airbender.Compiler.MaterializedNative.SubwordMemoryCached.native.model.value row column) ∧
      (∀ field ∈ Airbender.Compiler.HelperNative.SubwordMemoryCached.native.fields, (field.value (Airbender.Compiler.HelperNative.SubwordMemoryCached.native.sourceValues baseValue)).val < 524288) := by
  let initial := Airbender.Compiler.HelperValidityNative.SubwordMemoryCached.native.canonical sourceValue
  let extended := Airbender.Compiler.CounterFrameNative.SubwordMemoryCached.native.assigned initial counts
  have holds := Airbender.Compiler.CounterFrameNative.SubwordMemoryCached.native.source_preserved initial counts (Airbender.Compiler.HelperValidityNative.SubwordMemoryCached.native.source_holds sourceValue original clockValid)
  let full := Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.artifact.translation.extend extended
  let baseValue := Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.bank.materialize full (Airbender.Compiler.MaterializedNative.SubwordMemoryCached.native.model.baseOracle row fallback)
  have arithmetic := Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.full_arithmetic_extends extended holds
  have baseArithmetic := WireBank.materialize_gates Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.bank Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.bankRoundTrip full
    (Airbender.Compiler.MaterializedNative.SubwordMemoryCached.native.model.baseOracle row fallback) Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.artifact.gates arithmetic.2
  have inputAgreement (wire) : baseValue (Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.inputBank.address wire) = extended wire :=
    WireBank.materialize_source_input Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.bank Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.inputBank Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.artifact.projection
      Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.inputCoordinates Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.bankRoundTrip extended full arithmetic.1
      (Airbender.Compiler.MaterializedNative.SubwordMemoryCached.native.model.baseOracle row fallback) wire
  refine ⟨baseValue, Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.canonical hom challenges gamma baseValue, inputAgreement, baseArithmetic,
    Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.canonical_base hom challenges gamma baseValue,
    Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.canonical_affines hom challenges gamma baseValue baseArithmetic,
    Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.canonical_lookups hom challenges gamma baseValue,
    Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.canonical_products hom challenges gamma baseValue, ?_,
    native.materialized_cells Airbender.Compiler.MaterializedNative.SubwordMemoryCached.native.model row fallback full, ?_⟩
  · intro index
    have actual := inputAgreement (Airbender.Compiler.CounterFrameNative.SubwordMemoryCached.native.slots index)
    rw [Airbender.Compiler.CounterFrameNative.SubwordMemoryCached.native.slotsRoundTrip index] at actual
    exact actual.trans (Airbender.Compiler.CounterFrameNative.SubwordMemoryCached.native.counts_at initial counts index)
  · intro field member
    have same := Source.HelperField.transport_value field Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.helperPlacement Airbender.Compiler.HelperNative.SubwordMemoryCached.native.placement
      Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.inputBank Airbender.Compiler.MemoryNative.SubwordMemoryCached.native.bank (List.all_eq_true.mp Airbender.Compiler.HelperValidityNative.SubwordMemoryCached.native.transportChecked field member)
      extended baseValue inputAgreement
    change (field.value (Airbender.Compiler.HelperNative.SubwordMemoryCached.native.placement.project (baseValue ∘ Airbender.Compiler.MemoryNative.SubwordMemoryCached.native.bank.address))).val < 524288
    rw [same, Airbender.Compiler.CounterFrameNative.SubwordMemoryCached.native.helpers_preserved initial counts field member]
    exact Airbender.Compiler.HelperValidityNative.SubwordMemoryCached.native.helper_membership sourceValue primitives field member

end Airbender.Compiler.OracleFrameNative.SubwordMemoryCached
