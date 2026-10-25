import GKRProtocol.OracleFrameImport
import GKRProtocol.CounterFrameNative.MulDivUncached
import GKRProtocol.MaterializedNative.MulDivUncached

namespace Airbender.Compiler.OracleFrameNative.MulDivUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_lookup_oracle_frame native from "artifacts/compiler/mul-div-uncached.json"
  base_model Airbender.Compiler.FullArithmeticNative.MulDivUncached.native typing Airbender.Compiler.ConsumerNative.MulDivUncached.native.typing

theorem oracle_graph_extends {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (sourceValue : Fin 71 → Source.BaseField)
    (original : Satisfies (Airbender.Compiler.SourceContractNative.MulDivUncached.native.originals.map Expression.polynomial) sourceValue)
    (clockValid : Source.clockContract Airbender.Compiler.SourceContractNative.MulDivUncached.native.clock (Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.helperPlacement.memory.project sourceValue))
    (primitives : Airbender.Compiler.HelperValidityNative.MulDivUncached.native.profile.ExecutionValid (Airbender.Compiler.HelperValidityNative.MulDivUncached.native.execute.value (Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.helperPlacement.memory.project sourceValue))
      (Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.helperPlacement.memory.project sourceValue))
    (counts : Fin Airbender.Compiler.TableNative.MulDivUncached.native.multiplicityColumns.length → Source.BaseField)
    (row : Fin Airbender.Compiler.MaterializedNative.MulDivUncached.native.model.imported.data.length) (fallback : GKRAddress → Source.BaseField) :
    ∃ baseValue : GKRAddress → Source.BaseField, ∃ values : GKRAddress → R,
      (∀ wire, baseValue (Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.MulDivUncached.native.assigned (Airbender.Compiler.HelperValidityNative.MulDivUncached.native.canonical sourceValue) counts wire) ∧
      (∀ gate ∈ Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.artifact.gates, gate.expressionResidual (baseValue ∘ Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.bank.address) = 0) ∧
      (∀ address, Airbender.Compiler.FunctionalNative.MulDivUncached.native.isBase address = true → values address = hom (baseValue address)) ∧
      (∀ definition ∈ Airbender.Compiler.FunctionalNative.MulDivUncached.native.definitions, definition.Holds hom challenges values) ∧
      (∀ gate ∈ Airbender.Compiler.LookupNative.MulDivUncached.native.gates, gate.Holds hom challenges gamma values) ∧
      (∀ gate ∈ Airbender.Compiler.ProductNative.MulDivUncached.native.gates, gate.Holds hom challenges values) ∧
      (∀ index, baseValue (GKRAddress.BaseLayerWitness (Airbender.Compiler.TableNative.MulDivUncached.native.multiplicityColumns.get index)) = counts index) ∧
      (∀ column ∈ native.columns, baseValue column.address = Airbender.Compiler.MaterializedNative.MulDivUncached.native.model.value row column) ∧
      (∀ field ∈ Airbender.Compiler.HelperNative.MulDivUncached.native.fields, (field.value (Airbender.Compiler.HelperNative.MulDivUncached.native.sourceValues baseValue)).val < 524288) := by
  let initial := Airbender.Compiler.HelperValidityNative.MulDivUncached.native.canonical sourceValue
  let extended := Airbender.Compiler.CounterFrameNative.MulDivUncached.native.assigned initial counts
  have holds := Airbender.Compiler.CounterFrameNative.MulDivUncached.native.source_preserved initial counts (Airbender.Compiler.HelperValidityNative.MulDivUncached.native.source_holds sourceValue original clockValid)
  let full := Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.artifact.translation.extend extended
  let baseValue := Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.bank.materialize full (Airbender.Compiler.MaterializedNative.MulDivUncached.native.model.baseOracle row fallback)
  have arithmetic := Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.full_arithmetic_extends extended holds
  have baseArithmetic := WireBank.materialize_gates Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.bank Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.bankRoundTrip full
    (Airbender.Compiler.MaterializedNative.MulDivUncached.native.model.baseOracle row fallback) Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.artifact.gates arithmetic.2
  have inputAgreement (wire) : baseValue (Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.inputBank.address wire) = extended wire :=
    WireBank.materialize_source_input Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.bank Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.inputBank Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.artifact.projection
      Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.inputCoordinates Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.bankRoundTrip extended full arithmetic.1
      (Airbender.Compiler.MaterializedNative.MulDivUncached.native.model.baseOracle row fallback) wire
  refine ⟨baseValue, Airbender.Compiler.FunctionalNative.MulDivUncached.native.canonical hom challenges gamma baseValue, inputAgreement, baseArithmetic,
    Airbender.Compiler.FunctionalNative.MulDivUncached.native.canonical_base hom challenges gamma baseValue,
    Airbender.Compiler.FunctionalNative.MulDivUncached.native.canonical_affines hom challenges gamma baseValue baseArithmetic,
    Airbender.Compiler.FunctionalNative.MulDivUncached.native.canonical_lookups hom challenges gamma baseValue,
    Airbender.Compiler.FunctionalNative.MulDivUncached.native.canonical_products hom challenges gamma baseValue, ?_,
    native.materialized_cells Airbender.Compiler.MaterializedNative.MulDivUncached.native.model row fallback full, ?_⟩
  · intro index
    have actual := inputAgreement (Airbender.Compiler.CounterFrameNative.MulDivUncached.native.slots index)
    rw [Airbender.Compiler.CounterFrameNative.MulDivUncached.native.slotsRoundTrip index] at actual
    exact actual.trans (Airbender.Compiler.CounterFrameNative.MulDivUncached.native.counts_at initial counts index)
  · intro field member
    have same := Source.HelperField.transport_value field Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.helperPlacement Airbender.Compiler.HelperNative.MulDivUncached.native.placement
      Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.inputBank Airbender.Compiler.MemoryNative.MulDivUncached.native.bank (List.all_eq_true.mp Airbender.Compiler.HelperValidityNative.MulDivUncached.native.transportChecked field member)
      extended baseValue inputAgreement
    change (field.value (Airbender.Compiler.HelperNative.MulDivUncached.native.placement.project (baseValue ∘ Airbender.Compiler.MemoryNative.MulDivUncached.native.bank.address))).val < 524288
    rw [same, Airbender.Compiler.CounterFrameNative.MulDivUncached.native.helpers_preserved initial counts field member]
    exact Airbender.Compiler.HelperValidityNative.MulDivUncached.native.helper_membership sourceValue primitives field member

end Airbender.Compiler.OracleFrameNative.MulDivUncached
