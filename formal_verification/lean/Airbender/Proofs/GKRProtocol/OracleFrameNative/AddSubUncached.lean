import Airbender.Import.GKRProtocol.OracleFrameImport
import Airbender.Proofs.GKRProtocol.CounterFrameNative.AddSubUncached
import Airbender.Proofs.GKRProtocol.MaterializedNative.AddSubUncached

namespace Airbender.Compiler.OracleFrameNative.AddSubUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_lookup_oracle_frame native from "artifacts/compiler/add-sub-uncached.json"
  base_model Airbender.Compiler.FullArithmeticNative.AddSubUncached.native typing Airbender.Compiler.ConsumerNative.AddSubUncached.native.typing

theorem oracle_graph_extends {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (sourceValue : Fin 48 → Source.BaseField)
    (original : Satisfies (Airbender.Compiler.SourceContractNative.AddSubUncached.native.originals.map Expression.polynomial) sourceValue)
    (clockValid : Source.clockContract Airbender.Compiler.SourceContractNative.AddSubUncached.native.clock (Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.helperPlacement.memory.project sourceValue))
    (primitives : Airbender.Compiler.HelperValidityNative.AddSubUncached.native.profile.ExecutionValid (Airbender.Compiler.HelperValidityNative.AddSubUncached.native.execute.value (Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.helperPlacement.memory.project sourceValue))
      (Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.helperPlacement.memory.project sourceValue))
    (counts : Fin Airbender.Compiler.TableNative.AddSubUncached.native.multiplicityColumns.length → Source.BaseField)
    (row : Fin Airbender.Compiler.MaterializedNative.AddSubUncached.native.model.imported.data.length) (fallback : GKRAddress → Source.BaseField) :
    ∃ baseValue : GKRAddress → Source.BaseField, ∃ values : GKRAddress → R,
      (∀ wire, baseValue (Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.AddSubUncached.native.assigned (Airbender.Compiler.HelperValidityNative.AddSubUncached.native.canonical sourceValue) counts wire) ∧
      (∀ gate ∈ Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.artifact.gates, gate.expressionResidual (baseValue ∘ Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.bank.address) = 0) ∧
      (∀ address, Airbender.Compiler.FunctionalNative.AddSubUncached.native.isBase address = true → values address = hom (baseValue address)) ∧
      (∀ definition ∈ Airbender.Compiler.FunctionalNative.AddSubUncached.native.definitions, definition.Holds hom challenges values) ∧
      (∀ gate ∈ Airbender.Compiler.LookupNative.AddSubUncached.native.gates, gate.Holds hom challenges gamma values) ∧
      (∀ gate ∈ Airbender.Compiler.ProductNative.AddSubUncached.native.gates, gate.Holds hom challenges values) ∧
      (∀ index, baseValue (GKRAddress.BaseLayerWitness (Airbender.Compiler.TableNative.AddSubUncached.native.multiplicityColumns.get index)) = counts index) ∧
      (∀ column ∈ native.columns, baseValue column.address = Airbender.Compiler.MaterializedNative.AddSubUncached.native.model.value row column) ∧
      (∀ field ∈ Airbender.Compiler.HelperNative.AddSubUncached.native.fields, (field.value (Airbender.Compiler.HelperNative.AddSubUncached.native.sourceValues baseValue)).val < 524288) := by
  let initial := Airbender.Compiler.HelperValidityNative.AddSubUncached.native.canonical sourceValue
  let extended := Airbender.Compiler.CounterFrameNative.AddSubUncached.native.assigned initial counts
  have holds := Airbender.Compiler.CounterFrameNative.AddSubUncached.native.source_preserved initial counts (Airbender.Compiler.HelperValidityNative.AddSubUncached.native.source_holds sourceValue original clockValid)
  let full := Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.artifact.translation.extend extended
  let baseValue := Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.bank.materialize full (Airbender.Compiler.MaterializedNative.AddSubUncached.native.model.baseOracle row fallback)
  have arithmetic := Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.full_arithmetic_extends extended holds
  have baseArithmetic := WireBank.materialize_gates Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.bank Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.bankRoundTrip full
    (Airbender.Compiler.MaterializedNative.AddSubUncached.native.model.baseOracle row fallback) Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.artifact.gates arithmetic.2
  have inputAgreement (wire) : baseValue (Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.inputBank.address wire) = extended wire :=
    WireBank.materialize_source_input Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.bank Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.inputBank Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.artifact.projection
      Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.inputCoordinates Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.bankRoundTrip extended full arithmetic.1
      (Airbender.Compiler.MaterializedNative.AddSubUncached.native.model.baseOracle row fallback) wire
  refine ⟨baseValue, Airbender.Compiler.FunctionalNative.AddSubUncached.native.canonical hom challenges gamma baseValue, inputAgreement, baseArithmetic,
    Airbender.Compiler.FunctionalNative.AddSubUncached.native.canonical_base hom challenges gamma baseValue,
    Airbender.Compiler.FunctionalNative.AddSubUncached.native.canonical_affines hom challenges gamma baseValue baseArithmetic,
    Airbender.Compiler.FunctionalNative.AddSubUncached.native.canonical_lookups hom challenges gamma baseValue,
    Airbender.Compiler.FunctionalNative.AddSubUncached.native.canonical_products hom challenges gamma baseValue, ?_,
    native.materialized_cells Airbender.Compiler.MaterializedNative.AddSubUncached.native.model row fallback full, ?_⟩
  · intro index
    have actual := inputAgreement (Airbender.Compiler.CounterFrameNative.AddSubUncached.native.slots index)
    rw [Airbender.Compiler.CounterFrameNative.AddSubUncached.native.slotsRoundTrip index] at actual
    exact actual.trans (Airbender.Compiler.CounterFrameNative.AddSubUncached.native.counts_at initial counts index)
  · intro field member
    have same := Source.HelperField.transport_value field Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.helperPlacement Airbender.Compiler.HelperNative.AddSubUncached.native.placement
      Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.inputBank Airbender.Compiler.MemoryNative.AddSubUncached.native.bank (List.all_eq_true.mp Airbender.Compiler.HelperValidityNative.AddSubUncached.native.transportChecked field member)
      extended baseValue inputAgreement
    change (field.value (Airbender.Compiler.HelperNative.AddSubUncached.native.placement.project (baseValue ∘ Airbender.Compiler.MemoryNative.AddSubUncached.native.bank.address))).val < 524288
    rw [same, Airbender.Compiler.CounterFrameNative.AddSubUncached.native.helpers_preserved initial counts field member]
    exact Airbender.Compiler.HelperValidityNative.AddSubUncached.native.helper_membership sourceValue primitives field member

end Airbender.Compiler.OracleFrameNative.AddSubUncached
