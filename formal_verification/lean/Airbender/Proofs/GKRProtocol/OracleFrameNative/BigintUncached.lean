import Airbender.Import.GKRProtocol.OracleFrameImport
import Airbender.Proofs.GKRProtocol.CounterFrameNative.BigintUncached
import Airbender.Proofs.GKRProtocol.MaterializedNative.BigintUncached

namespace Airbender.Compiler.OracleFrameNative.BigintUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_lookup_oracle_frame native from "artifacts/compiler/bigint-uncached.json"
  base_model Airbender.Compiler.FullArithmeticNative.BigintUncached.native typing Airbender.Compiler.ConsumerNative.BigintUncached.native.typing

theorem oracle_graph_extends {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (sourceValue : Fin 276 → Source.BaseField)
    (original : Satisfies (Airbender.Compiler.SourceContractNative.BigintUncached.native.originals.map Expression.polynomial) sourceValue)
    (clockValid : Source.clockContract Airbender.Compiler.SourceContractNative.BigintUncached.native.clock (Airbender.Compiler.FullArithmeticNative.BigintUncached.native.helperPlacement.memory.project sourceValue))
    (primitives : Airbender.Compiler.HelperValidityNative.BigintUncached.native.profile.ExecutionValid (Airbender.Compiler.HelperValidityNative.BigintUncached.native.execute.value (Airbender.Compiler.FullArithmeticNative.BigintUncached.native.helperPlacement.memory.project sourceValue))
      (Airbender.Compiler.FullArithmeticNative.BigintUncached.native.helperPlacement.memory.project sourceValue))
    (counts : Fin Airbender.Compiler.TableNative.BigintUncached.native.multiplicityColumns.length → Source.BaseField)
    (row : Fin Airbender.Compiler.MaterializedNative.BigintUncached.native.model.imported.data.length) (fallback : GKRAddress → Source.BaseField) :
    ∃ baseValue : GKRAddress → Source.BaseField, ∃ values : GKRAddress → R,
      (∀ wire, baseValue (Airbender.Compiler.FullArithmeticNative.BigintUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BigintUncached.native.assigned (Airbender.Compiler.HelperValidityNative.BigintUncached.native.canonical sourceValue) counts wire) ∧
      (∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.artifact.gates, gate.expressionResidual (baseValue ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank.address) = 0) ∧
      (∀ address, Airbender.Compiler.FunctionalNative.BigintUncached.native.isBase address = true → values address = hom (baseValue address)) ∧
      (∀ definition ∈ Airbender.Compiler.FunctionalNative.BigintUncached.native.definitions, definition.Holds hom challenges values) ∧
      (∀ gate ∈ Airbender.Compiler.LookupNative.BigintUncached.native.gates, gate.Holds hom challenges gamma values) ∧
      (∀ gate ∈ Airbender.Compiler.ProductNative.BigintUncached.native.gates, gate.Holds hom challenges values) ∧
      (∀ index, baseValue (GKRAddress.BaseLayerWitness (Airbender.Compiler.TableNative.BigintUncached.native.multiplicityColumns.get index)) = counts index) ∧
      (∀ column ∈ native.columns, baseValue column.address = Airbender.Compiler.MaterializedNative.BigintUncached.native.model.value row column) ∧
      (∀ field ∈ Airbender.Compiler.HelperNative.BigintUncached.native.fields, (field.value (Airbender.Compiler.HelperNative.BigintUncached.native.sourceValues baseValue)).val < 524288) := by
  let initial := Airbender.Compiler.HelperValidityNative.BigintUncached.native.canonical sourceValue
  let extended := Airbender.Compiler.CounterFrameNative.BigintUncached.native.assigned initial counts
  have holds := Airbender.Compiler.CounterFrameNative.BigintUncached.native.source_preserved initial counts (Airbender.Compiler.HelperValidityNative.BigintUncached.native.source_holds sourceValue original clockValid)
  let full := Airbender.Compiler.FullArithmeticNative.BigintUncached.native.artifact.translation.extend extended
  let baseValue := Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank.materialize full (Airbender.Compiler.MaterializedNative.BigintUncached.native.model.baseOracle row fallback)
  have arithmetic := Airbender.Compiler.FullArithmeticNative.BigintUncached.native.full_arithmetic_extends extended holds
  have baseArithmetic := WireBank.materialize_gates Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bankRoundTrip full
    (Airbender.Compiler.MaterializedNative.BigintUncached.native.model.baseOracle row fallback) Airbender.Compiler.FullArithmeticNative.BigintUncached.native.artifact.gates arithmetic.2
  have inputAgreement (wire) : baseValue (Airbender.Compiler.FullArithmeticNative.BigintUncached.native.inputBank.address wire) = extended wire :=
    WireBank.materialize_source_input Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.FullArithmeticNative.BigintUncached.native.inputBank Airbender.Compiler.FullArithmeticNative.BigintUncached.native.artifact.projection
      Airbender.Compiler.FullArithmeticNative.BigintUncached.native.inputCoordinates Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bankRoundTrip extended full arithmetic.1
      (Airbender.Compiler.MaterializedNative.BigintUncached.native.model.baseOracle row fallback) wire
  refine ⟨baseValue, Airbender.Compiler.FunctionalNative.BigintUncached.native.canonical hom challenges gamma baseValue, inputAgreement, baseArithmetic,
    Airbender.Compiler.FunctionalNative.BigintUncached.native.canonical_base hom challenges gamma baseValue,
    Airbender.Compiler.FunctionalNative.BigintUncached.native.canonical_affines hom challenges gamma baseValue baseArithmetic,
    Airbender.Compiler.FunctionalNative.BigintUncached.native.canonical_lookups hom challenges gamma baseValue,
    Airbender.Compiler.FunctionalNative.BigintUncached.native.canonical_products hom challenges gamma baseValue, ?_,
    native.materialized_cells Airbender.Compiler.MaterializedNative.BigintUncached.native.model row fallback full, ?_⟩
  · intro index
    have actual := inputAgreement (Airbender.Compiler.CounterFrameNative.BigintUncached.native.slots index)
    rw [Airbender.Compiler.CounterFrameNative.BigintUncached.native.slotsRoundTrip index] at actual
    exact actual.trans (Airbender.Compiler.CounterFrameNative.BigintUncached.native.counts_at initial counts index)
  · intro field member
    have same := Source.HelperField.transport_value field Airbender.Compiler.FullArithmeticNative.BigintUncached.native.helperPlacement Airbender.Compiler.HelperNative.BigintUncached.native.placement
      Airbender.Compiler.FullArithmeticNative.BigintUncached.native.inputBank Airbender.Compiler.MemoryNative.BigintUncached.native.bank (List.all_eq_true.mp Airbender.Compiler.HelperValidityNative.BigintUncached.native.transportChecked field member)
      extended baseValue inputAgreement
    change (field.value (Airbender.Compiler.HelperNative.BigintUncached.native.placement.project (baseValue ∘ Airbender.Compiler.MemoryNative.BigintUncached.native.bank.address))).val < 524288
    rw [same, Airbender.Compiler.CounterFrameNative.BigintUncached.native.helpers_preserved initial counts field member]
    exact Airbender.Compiler.HelperValidityNative.BigintUncached.native.helper_membership sourceValue primitives field member

end Airbender.Compiler.OracleFrameNative.BigintUncached
