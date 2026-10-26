import Airbender.Import.GKRProtocol.OracleFrameImport
import Airbender.Proofs.GKRProtocol.CounterFrameNative.KeccakCached
import Airbender.Proofs.GKRProtocol.MaterializedNative.KeccakCached

namespace Airbender.Compiler.OracleFrameNative.KeccakCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_lookup_oracle_frame native from "artifacts/compiler/keccak-cached.json"
  base_model Airbender.Compiler.FullArithmeticNative.KeccakCached.native typing Airbender.Compiler.ConsumerNative.KeccakCached.native.typing

theorem oracle_graph_extends {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (sourceValue : Fin 267 → Source.BaseField)
    (original : Satisfies (Airbender.Compiler.SourceContractNative.KeccakCached.native.originals.map Expression.polynomial) sourceValue)
    (clockValid : Source.clockContract Airbender.Compiler.SourceContractNative.KeccakCached.native.clock (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.helperPlacement.memory.project sourceValue))
    (primitives : Airbender.Compiler.HelperValidityNative.KeccakCached.native.profile.ExecutionValid (Airbender.Compiler.HelperValidityNative.KeccakCached.native.execute.value (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.helperPlacement.memory.project sourceValue))
      (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.helperPlacement.memory.project sourceValue))
    (counts : Fin Airbender.Compiler.TableNative.KeccakCached.native.multiplicityColumns.length → Source.BaseField)
    (row : Fin Airbender.Compiler.MaterializedNative.KeccakCached.native.model.imported.data.length) (fallback : GKRAddress → Source.BaseField) :
    ∃ baseValue : GKRAddress → Source.BaseField, ∃ values : GKRAddress → R,
      (∀ wire, baseValue (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.KeccakCached.native.assigned (Airbender.Compiler.HelperValidityNative.KeccakCached.native.canonical sourceValue) counts wire) ∧
      (∀ gate ∈ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.artifact.gates, gate.expressionResidual (baseValue ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address) = 0) ∧
      (∀ address, Airbender.Compiler.FunctionalNative.KeccakCached.native.isBase address = true → values address = hom (baseValue address)) ∧
      (∀ definition ∈ Airbender.Compiler.FunctionalNative.KeccakCached.native.definitions, definition.Holds hom challenges values) ∧
      (∀ gate ∈ Airbender.Compiler.LookupNative.KeccakCached.native.gates, gate.Holds hom challenges gamma values) ∧
      (∀ gate ∈ Airbender.Compiler.ProductNative.KeccakCached.native.gates, gate.Holds hom challenges values) ∧
      (∀ index, baseValue (GKRAddress.BaseLayerWitness (Airbender.Compiler.TableNative.KeccakCached.native.multiplicityColumns.get index)) = counts index) ∧
      (∀ column ∈ native.columns, baseValue column.address = Airbender.Compiler.MaterializedNative.KeccakCached.native.model.value row column) ∧
      (∀ field ∈ Airbender.Compiler.HelperNative.KeccakCached.native.fields, (field.value (Airbender.Compiler.HelperNative.KeccakCached.native.sourceValues baseValue)).val < 524288) := by
  let initial := Airbender.Compiler.HelperValidityNative.KeccakCached.native.canonical sourceValue
  let extended := Airbender.Compiler.CounterFrameNative.KeccakCached.native.assigned initial counts
  have holds := Airbender.Compiler.CounterFrameNative.KeccakCached.native.source_preserved initial counts (Airbender.Compiler.HelperValidityNative.KeccakCached.native.source_holds sourceValue original clockValid)
  let full := Airbender.Compiler.FullArithmeticNative.KeccakCached.native.artifact.translation.extend extended
  let baseValue := Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.materialize full (Airbender.Compiler.MaterializedNative.KeccakCached.native.model.baseOracle row fallback)
  have arithmetic := Airbender.Compiler.FullArithmeticNative.KeccakCached.native.full_arithmetic_extends extended holds
  have baseArithmetic := WireBank.materialize_gates Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bankRoundTrip full
    (Airbender.Compiler.MaterializedNative.KeccakCached.native.model.baseOracle row fallback) Airbender.Compiler.FullArithmeticNative.KeccakCached.native.artifact.gates arithmetic.2
  have inputAgreement (wire) : baseValue (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.inputBank.address wire) = extended wire :=
    WireBank.materialize_source_input Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank Airbender.Compiler.FullArithmeticNative.KeccakCached.native.inputBank Airbender.Compiler.FullArithmeticNative.KeccakCached.native.artifact.projection
      Airbender.Compiler.FullArithmeticNative.KeccakCached.native.inputCoordinates Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bankRoundTrip extended full arithmetic.1
      (Airbender.Compiler.MaterializedNative.KeccakCached.native.model.baseOracle row fallback) wire
  refine ⟨baseValue, Airbender.Compiler.FunctionalNative.KeccakCached.native.canonical hom challenges gamma baseValue, inputAgreement, baseArithmetic,
    Airbender.Compiler.FunctionalNative.KeccakCached.native.canonical_base hom challenges gamma baseValue,
    Airbender.Compiler.FunctionalNative.KeccakCached.native.canonical_affines hom challenges gamma baseValue baseArithmetic,
    Airbender.Compiler.FunctionalNative.KeccakCached.native.canonical_lookups hom challenges gamma baseValue,
    Airbender.Compiler.FunctionalNative.KeccakCached.native.canonical_products hom challenges gamma baseValue, ?_,
    native.materialized_cells Airbender.Compiler.MaterializedNative.KeccakCached.native.model row fallback full, ?_⟩
  · intro index
    have actual := inputAgreement (Airbender.Compiler.CounterFrameNative.KeccakCached.native.slots index)
    rw [Airbender.Compiler.CounterFrameNative.KeccakCached.native.slotsRoundTrip index] at actual
    exact actual.trans (Airbender.Compiler.CounterFrameNative.KeccakCached.native.counts_at initial counts index)
  · intro field member
    have same := Source.HelperField.transport_value field Airbender.Compiler.FullArithmeticNative.KeccakCached.native.helperPlacement Airbender.Compiler.HelperNative.KeccakCached.native.placement
      Airbender.Compiler.FullArithmeticNative.KeccakCached.native.inputBank Airbender.Compiler.MemoryNative.KeccakCached.native.bank (List.all_eq_true.mp Airbender.Compiler.HelperValidityNative.KeccakCached.native.transportChecked field member)
      extended baseValue inputAgreement
    change (field.value (Airbender.Compiler.HelperNative.KeccakCached.native.placement.project (baseValue ∘ Airbender.Compiler.MemoryNative.KeccakCached.native.bank.address))).val < 524288
    rw [same, Airbender.Compiler.CounterFrameNative.KeccakCached.native.helpers_preserved initial counts field member]
    exact Airbender.Compiler.HelperValidityNative.KeccakCached.native.helper_membership sourceValue primitives field member

end Airbender.Compiler.OracleFrameNative.KeccakCached
