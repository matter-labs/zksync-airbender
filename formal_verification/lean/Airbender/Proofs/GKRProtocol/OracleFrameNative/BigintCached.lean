import Airbender.Import.GKRProtocol.OracleFrameImport
import Airbender.Proofs.GKRProtocol.CounterFrameNative.BigintCached
import Airbender.Proofs.GKRProtocol.MaterializedNative.BigintCached

namespace Airbender.Compiler.OracleFrameNative.BigintCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_lookup_oracle_frame native from "artifacts/compiler/bigint-cached.json"
  base_model Airbender.Compiler.FullArithmeticNative.BigintCached.native typing Airbender.Compiler.ConsumerNative.BigintCached.native.typing

theorem oracle_graph_extends {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (sourceValue : Fin 277 → Source.BaseField)
    (original : Satisfies (Airbender.Compiler.SourceContractNative.BigintCached.native.originals.map Expression.polynomial) sourceValue)
    (clockValid : Source.clockContract Airbender.Compiler.SourceContractNative.BigintCached.native.clock (Airbender.Compiler.FullArithmeticNative.BigintCached.native.helperPlacement.memory.project sourceValue))
    (primitives : Airbender.Compiler.HelperValidityNative.BigintCached.native.profile.ExecutionValid (Airbender.Compiler.HelperValidityNative.BigintCached.native.execute.value (Airbender.Compiler.FullArithmeticNative.BigintCached.native.helperPlacement.memory.project sourceValue))
      (Airbender.Compiler.FullArithmeticNative.BigintCached.native.helperPlacement.memory.project sourceValue))
    (counts : Fin Airbender.Compiler.TableNative.BigintCached.native.multiplicityColumns.length → Source.BaseField)
    (row : Fin Airbender.Compiler.MaterializedNative.BigintCached.native.model.imported.data.length) (fallback : GKRAddress → Source.BaseField) :
    ∃ baseValue : GKRAddress → Source.BaseField, ∃ values : GKRAddress → R,
      (∀ wire, baseValue (Airbender.Compiler.FullArithmeticNative.BigintCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BigintCached.native.assigned (Airbender.Compiler.HelperValidityNative.BigintCached.native.canonical sourceValue) counts wire) ∧
      (∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintCached.native.artifact.gates, gate.expressionResidual (baseValue ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) = 0) ∧
      (∀ address, Airbender.Compiler.FunctionalNative.BigintCached.native.isBase address = true → values address = hom (baseValue address)) ∧
      (∀ definition ∈ Airbender.Compiler.FunctionalNative.BigintCached.native.definitions, definition.Holds hom challenges values) ∧
      (∀ gate ∈ Airbender.Compiler.LookupNative.BigintCached.native.gates, gate.Holds hom challenges gamma values) ∧
      (∀ gate ∈ Airbender.Compiler.ProductNative.BigintCached.native.gates, gate.Holds hom challenges values) ∧
      (∀ index, baseValue (GKRAddress.BaseLayerWitness (Airbender.Compiler.TableNative.BigintCached.native.multiplicityColumns.get index)) = counts index) ∧
      (∀ column ∈ native.columns, baseValue column.address = Airbender.Compiler.MaterializedNative.BigintCached.native.model.value row column) ∧
      (∀ field ∈ Airbender.Compiler.HelperNative.BigintCached.native.fields, (field.value (Airbender.Compiler.HelperNative.BigintCached.native.sourceValues baseValue)).val < 524288) := by
  let initial := Airbender.Compiler.HelperValidityNative.BigintCached.native.canonical sourceValue
  let extended := Airbender.Compiler.CounterFrameNative.BigintCached.native.assigned initial counts
  have holds := Airbender.Compiler.CounterFrameNative.BigintCached.native.source_preserved initial counts (Airbender.Compiler.HelperValidityNative.BigintCached.native.source_holds sourceValue original clockValid)
  let full := Airbender.Compiler.FullArithmeticNative.BigintCached.native.artifact.translation.extend extended
  let baseValue := Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.materialize full (Airbender.Compiler.MaterializedNative.BigintCached.native.model.baseOracle row fallback)
  have arithmetic := Airbender.Compiler.FullArithmeticNative.BigintCached.native.full_arithmetic_extends extended holds
  have baseArithmetic := WireBank.materialize_gates Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank Airbender.Compiler.FullArithmeticNative.BigintCached.native.bankRoundTrip full
    (Airbender.Compiler.MaterializedNative.BigintCached.native.model.baseOracle row fallback) Airbender.Compiler.FullArithmeticNative.BigintCached.native.artifact.gates arithmetic.2
  have inputAgreement (wire) : baseValue (Airbender.Compiler.FullArithmeticNative.BigintCached.native.inputBank.address wire) = extended wire :=
    WireBank.materialize_source_input Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank Airbender.Compiler.FullArithmeticNative.BigintCached.native.inputBank Airbender.Compiler.FullArithmeticNative.BigintCached.native.artifact.projection
      Airbender.Compiler.FullArithmeticNative.BigintCached.native.inputCoordinates Airbender.Compiler.FullArithmeticNative.BigintCached.native.bankRoundTrip extended full arithmetic.1
      (Airbender.Compiler.MaterializedNative.BigintCached.native.model.baseOracle row fallback) wire
  refine ⟨baseValue, Airbender.Compiler.FunctionalNative.BigintCached.native.canonical hom challenges gamma baseValue, inputAgreement, baseArithmetic,
    Airbender.Compiler.FunctionalNative.BigintCached.native.canonical_base hom challenges gamma baseValue,
    Airbender.Compiler.FunctionalNative.BigintCached.native.canonical_affines hom challenges gamma baseValue baseArithmetic,
    Airbender.Compiler.FunctionalNative.BigintCached.native.canonical_lookups hom challenges gamma baseValue,
    Airbender.Compiler.FunctionalNative.BigintCached.native.canonical_products hom challenges gamma baseValue, ?_,
    native.materialized_cells Airbender.Compiler.MaterializedNative.BigintCached.native.model row fallback full, ?_⟩
  · intro index
    have actual := inputAgreement (Airbender.Compiler.CounterFrameNative.BigintCached.native.slots index)
    rw [Airbender.Compiler.CounterFrameNative.BigintCached.native.slotsRoundTrip index] at actual
    exact actual.trans (Airbender.Compiler.CounterFrameNative.BigintCached.native.counts_at initial counts index)
  · intro field member
    have same := Source.HelperField.transport_value field Airbender.Compiler.FullArithmeticNative.BigintCached.native.helperPlacement Airbender.Compiler.HelperNative.BigintCached.native.placement
      Airbender.Compiler.FullArithmeticNative.BigintCached.native.inputBank Airbender.Compiler.MemoryNative.BigintCached.native.bank (List.all_eq_true.mp Airbender.Compiler.HelperValidityNative.BigintCached.native.transportChecked field member)
      extended baseValue inputAgreement
    change (field.value (Airbender.Compiler.HelperNative.BigintCached.native.placement.project (baseValue ∘ Airbender.Compiler.MemoryNative.BigintCached.native.bank.address))).val < 524288
    rw [same, Airbender.Compiler.CounterFrameNative.BigintCached.native.helpers_preserved initial counts field member]
    exact Airbender.Compiler.HelperValidityNative.BigintCached.native.helper_membership sourceValue primitives field member

end Airbender.Compiler.OracleFrameNative.BigintCached
