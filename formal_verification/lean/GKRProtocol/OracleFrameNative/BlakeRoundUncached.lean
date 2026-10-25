import GKRProtocol.OracleFrameImport
import GKRProtocol.CounterFrameNative.BlakeRoundUncached
import GKRProtocol.MaterializedNative.BlakeRoundUncached

namespace Airbender.Compiler.OracleFrameNative.BlakeRoundUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_lookup_oracle_frame native from "artifacts/compiler/blake-round-uncached.json"
  base_model Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native typing Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing

theorem oracle_graph_extends {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (sourceValue : Fin 763 → Source.BaseField)
    (original : Satisfies (Airbender.Compiler.SourceContractNative.BlakeRoundUncached.native.originals.map Expression.polynomial) sourceValue)
    (clockValid : Source.clockContract Airbender.Compiler.SourceContractNative.BlakeRoundUncached.native.clock (Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.helperPlacement.memory.project sourceValue))
    (primitives : Airbender.Compiler.HelperValidityNative.BlakeRoundUncached.native.profile.ExecutionValid (Airbender.Compiler.HelperValidityNative.BlakeRoundUncached.native.execute.value (Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.helperPlacement.memory.project sourceValue))
      (Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.helperPlacement.memory.project sourceValue))
    (counts : Fin Airbender.Compiler.TableNative.BlakeRoundUncached.native.multiplicityColumns.length → Source.BaseField)
    (row : Fin Airbender.Compiler.MaterializedNative.BlakeRoundUncached.native.model.imported.data.length) (fallback : GKRAddress → Source.BaseField) :
    ∃ baseValue : GKRAddress → Source.BaseField, ∃ values : GKRAddress → R,
      (∀ wire, baseValue (Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BlakeRoundUncached.native.assigned (Airbender.Compiler.HelperValidityNative.BlakeRoundUncached.native.canonical sourceValue) counts wire) ∧
      (∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.artifact.gates, gate.expressionResidual (baseValue ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.bank.address) = 0) ∧
      (∀ address, Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.isBase address = true → values address = hom (baseValue address)) ∧
      (∀ definition ∈ Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.definitions, definition.Holds hom challenges values) ∧
      (∀ gate ∈ Airbender.Compiler.LookupNative.BlakeRoundUncached.native.gates, gate.Holds hom challenges gamma values) ∧
      (∀ gate ∈ Airbender.Compiler.ProductNative.BlakeRoundUncached.native.gates, gate.Holds hom challenges values) ∧
      (∀ index, baseValue (GKRAddress.BaseLayerWitness (Airbender.Compiler.TableNative.BlakeRoundUncached.native.multiplicityColumns.get index)) = counts index) ∧
      (∀ column ∈ native.columns, baseValue column.address = Airbender.Compiler.MaterializedNative.BlakeRoundUncached.native.model.value row column) ∧
      (∀ field ∈ Airbender.Compiler.HelperNative.BlakeRoundUncached.native.fields, (field.value (Airbender.Compiler.HelperNative.BlakeRoundUncached.native.sourceValues baseValue)).val < 524288) := by
  let initial := Airbender.Compiler.HelperValidityNative.BlakeRoundUncached.native.canonical sourceValue
  let extended := Airbender.Compiler.CounterFrameNative.BlakeRoundUncached.native.assigned initial counts
  have holds := Airbender.Compiler.CounterFrameNative.BlakeRoundUncached.native.source_preserved initial counts (Airbender.Compiler.HelperValidityNative.BlakeRoundUncached.native.source_holds sourceValue original clockValid)
  let full := Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.artifact.translation.extend extended
  let baseValue := Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.bank.materialize full (Airbender.Compiler.MaterializedNative.BlakeRoundUncached.native.model.baseOracle row fallback)
  have arithmetic := Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.full_arithmetic_extends extended holds
  have baseArithmetic := WireBank.materialize_gates Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.bank Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.bankRoundTrip full
    (Airbender.Compiler.MaterializedNative.BlakeRoundUncached.native.model.baseOracle row fallback) Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.artifact.gates arithmetic.2
  have inputAgreement (wire) : baseValue (Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.inputBank.address wire) = extended wire :=
    WireBank.materialize_source_input Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.bank Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.inputBank Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.artifact.projection
      Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.inputCoordinates Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.bankRoundTrip extended full arithmetic.1
      (Airbender.Compiler.MaterializedNative.BlakeRoundUncached.native.model.baseOracle row fallback) wire
  refine ⟨baseValue, Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.canonical hom challenges gamma baseValue, inputAgreement, baseArithmetic,
    Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.canonical_base hom challenges gamma baseValue,
    Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.canonical_affines hom challenges gamma baseValue baseArithmetic,
    Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.canonical_lookups hom challenges gamma baseValue,
    Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.canonical_products hom challenges gamma baseValue, ?_,
    native.materialized_cells Airbender.Compiler.MaterializedNative.BlakeRoundUncached.native.model row fallback full, ?_⟩
  · intro index
    have actual := inputAgreement (Airbender.Compiler.CounterFrameNative.BlakeRoundUncached.native.slots index)
    rw [Airbender.Compiler.CounterFrameNative.BlakeRoundUncached.native.slotsRoundTrip index] at actual
    exact actual.trans (Airbender.Compiler.CounterFrameNative.BlakeRoundUncached.native.counts_at initial counts index)
  · intro field member
    have same := Source.HelperField.transport_value field Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.helperPlacement Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement
      Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.inputBank Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank (List.all_eq_true.mp Airbender.Compiler.HelperValidityNative.BlakeRoundUncached.native.transportChecked field member)
      extended baseValue inputAgreement
    change (field.value (Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement.project (baseValue ∘ Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank.address))).val < 524288
    rw [same, Airbender.Compiler.CounterFrameNative.BlakeRoundUncached.native.helpers_preserved initial counts field member]
    exact Airbender.Compiler.HelperValidityNative.BlakeRoundUncached.native.helper_membership sourceValue primitives field member

end Airbender.Compiler.OracleFrameNative.BlakeRoundUncached
