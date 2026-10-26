import Airbender.Import.GKRProtocol.OracleFrameImport
import Airbender.Proofs.GKRProtocol.CounterFrameNative.SubwordMemoryUncached
import Airbender.Proofs.GKRProtocol.MaterializedNative.SubwordMemoryUncached

namespace Airbender.Compiler.OracleFrameNative.SubwordMemoryUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_lookup_oracle_frame native from "artifacts/compiler/subword-memory-uncached.json"
  base_model Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native typing Airbender.Compiler.ConsumerNative.SubwordMemoryUncached.native.typing

theorem oracle_graph_extends {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (sourceValue : Fin 68 → Source.BaseField)
    (original : Satisfies (Airbender.Compiler.SourceContractNative.SubwordMemoryUncached.native.originals.map Expression.polynomial) sourceValue)
    (clockValid : Source.clockContract Airbender.Compiler.SourceContractNative.SubwordMemoryUncached.native.clock (Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.helperPlacement.memory.project sourceValue))
    (primitives : Airbender.Compiler.HelperValidityNative.SubwordMemoryUncached.native.profile.ExecutionValid (Airbender.Compiler.HelperValidityNative.SubwordMemoryUncached.native.execute.value (Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.helperPlacement.memory.project sourceValue))
      (Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.helperPlacement.memory.project sourceValue))
    (counts : Fin Airbender.Compiler.TableNative.SubwordMemoryUncached.native.multiplicityColumns.length → Source.BaseField)
    (row : Fin Airbender.Compiler.MaterializedNative.SubwordMemoryUncached.native.model.imported.data.length) (fallback : GKRAddress → Source.BaseField) :
    ∃ baseValue : GKRAddress → Source.BaseField, ∃ values : GKRAddress → R,
      (∀ wire, baseValue (Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.SubwordMemoryUncached.native.assigned (Airbender.Compiler.HelperValidityNative.SubwordMemoryUncached.native.canonical sourceValue) counts wire) ∧
      (∀ gate ∈ Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.artifact.gates, gate.expressionResidual (baseValue ∘ Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.bank.address) = 0) ∧
      (∀ address, Airbender.Compiler.FunctionalNative.SubwordMemoryUncached.native.isBase address = true → values address = hom (baseValue address)) ∧
      (∀ definition ∈ Airbender.Compiler.FunctionalNative.SubwordMemoryUncached.native.definitions, definition.Holds hom challenges values) ∧
      (∀ gate ∈ Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.gates, gate.Holds hom challenges gamma values) ∧
      (∀ gate ∈ Airbender.Compiler.ProductNative.SubwordMemoryUncached.native.gates, gate.Holds hom challenges values) ∧
      (∀ index, baseValue (GKRAddress.BaseLayerWitness (Airbender.Compiler.TableNative.SubwordMemoryUncached.native.multiplicityColumns.get index)) = counts index) ∧
      (∀ column ∈ native.columns, baseValue column.address = Airbender.Compiler.MaterializedNative.SubwordMemoryUncached.native.model.value row column) ∧
      (∀ field ∈ Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.fields, (field.value (Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.sourceValues baseValue)).val < 524288) := by
  let initial := Airbender.Compiler.HelperValidityNative.SubwordMemoryUncached.native.canonical sourceValue
  let extended := Airbender.Compiler.CounterFrameNative.SubwordMemoryUncached.native.assigned initial counts
  have holds := Airbender.Compiler.CounterFrameNative.SubwordMemoryUncached.native.source_preserved initial counts (Airbender.Compiler.HelperValidityNative.SubwordMemoryUncached.native.source_holds sourceValue original clockValid)
  let full := Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.artifact.translation.extend extended
  let baseValue := Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.bank.materialize full (Airbender.Compiler.MaterializedNative.SubwordMemoryUncached.native.model.baseOracle row fallback)
  have arithmetic := Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.full_arithmetic_extends extended holds
  have baseArithmetic := WireBank.materialize_gates Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.bank Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.bankRoundTrip full
    (Airbender.Compiler.MaterializedNative.SubwordMemoryUncached.native.model.baseOracle row fallback) Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.artifact.gates arithmetic.2
  have inputAgreement (wire) : baseValue (Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.inputBank.address wire) = extended wire :=
    WireBank.materialize_source_input Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.bank Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.inputBank Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.artifact.projection
      Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.inputCoordinates Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.bankRoundTrip extended full arithmetic.1
      (Airbender.Compiler.MaterializedNative.SubwordMemoryUncached.native.model.baseOracle row fallback) wire
  refine ⟨baseValue, Airbender.Compiler.FunctionalNative.SubwordMemoryUncached.native.canonical hom challenges gamma baseValue, inputAgreement, baseArithmetic,
    Airbender.Compiler.FunctionalNative.SubwordMemoryUncached.native.canonical_base hom challenges gamma baseValue,
    Airbender.Compiler.FunctionalNative.SubwordMemoryUncached.native.canonical_affines hom challenges gamma baseValue baseArithmetic,
    Airbender.Compiler.FunctionalNative.SubwordMemoryUncached.native.canonical_lookups hom challenges gamma baseValue,
    Airbender.Compiler.FunctionalNative.SubwordMemoryUncached.native.canonical_products hom challenges gamma baseValue, ?_,
    native.materialized_cells Airbender.Compiler.MaterializedNative.SubwordMemoryUncached.native.model row fallback full, ?_⟩
  · intro index
    have actual := inputAgreement (Airbender.Compiler.CounterFrameNative.SubwordMemoryUncached.native.slots index)
    rw [Airbender.Compiler.CounterFrameNative.SubwordMemoryUncached.native.slotsRoundTrip index] at actual
    exact actual.trans (Airbender.Compiler.CounterFrameNative.SubwordMemoryUncached.native.counts_at initial counts index)
  · intro field member
    have same := Source.HelperField.transport_value field Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.helperPlacement Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.placement
      Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.inputBank Airbender.Compiler.MemoryNative.SubwordMemoryUncached.native.bank (List.all_eq_true.mp Airbender.Compiler.HelperValidityNative.SubwordMemoryUncached.native.transportChecked field member)
      extended baseValue inputAgreement
    change (field.value (Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.placement.project (baseValue ∘ Airbender.Compiler.MemoryNative.SubwordMemoryUncached.native.bank.address))).val < 524288
    rw [same, Airbender.Compiler.CounterFrameNative.SubwordMemoryUncached.native.helpers_preserved initial counts field member]
    exact Airbender.Compiler.HelperValidityNative.SubwordMemoryUncached.native.helper_membership sourceValue primitives field member

end Airbender.Compiler.OracleFrameNative.SubwordMemoryUncached
