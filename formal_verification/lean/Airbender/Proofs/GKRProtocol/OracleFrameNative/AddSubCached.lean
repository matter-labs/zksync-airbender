import Airbender.Import.GKRProtocol.OracleFrameImport
import Airbender.Proofs.GKRProtocol.CounterFrameNative.AddSubCached
import Airbender.Proofs.GKRProtocol.MaterializedNative.AddSubCached

namespace Airbender.Compiler.OracleFrameNative.AddSubCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_lookup_oracle_frame native from "artifacts/compiler/add-sub-cached.json"
  base_model Airbender.Compiler.FullArithmeticNative.AddSubCached.native typing Airbender.Compiler.ConsumerNative.AddSubCached.native.typing

theorem oracle_graph_extends {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (sourceValue : Fin 48 → Source.BaseField)
    (original : Satisfies (Airbender.Compiler.SourceContractNative.AddSubCached.native.originals.map Expression.polynomial) sourceValue)
    (clockValid : Source.clockContract Airbender.Compiler.SourceContractNative.AddSubCached.native.clock (Airbender.Compiler.FullArithmeticNative.AddSubCached.native.helperPlacement.memory.project sourceValue))
    (primitives : Airbender.Compiler.HelperValidityNative.AddSubCached.native.profile.ExecutionValid (Airbender.Compiler.HelperValidityNative.AddSubCached.native.execute.value (Airbender.Compiler.FullArithmeticNative.AddSubCached.native.helperPlacement.memory.project sourceValue))
      (Airbender.Compiler.FullArithmeticNative.AddSubCached.native.helperPlacement.memory.project sourceValue))
    (counts : Fin Airbender.Compiler.TableNative.AddSubCached.native.multiplicityColumns.length → Source.BaseField)
    (row : Fin Airbender.Compiler.MaterializedNative.AddSubCached.native.model.imported.data.length) (fallback : GKRAddress → Source.BaseField) :
    ∃ baseValue : GKRAddress → Source.BaseField, ∃ values : GKRAddress → R,
      (∀ wire, baseValue (Airbender.Compiler.FullArithmeticNative.AddSubCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.AddSubCached.native.assigned (Airbender.Compiler.HelperValidityNative.AddSubCached.native.canonical sourceValue) counts wire) ∧
      (∀ gate ∈ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.artifact.gates, gate.expressionResidual (baseValue ∘ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address) = 0) ∧
      (∀ address, Airbender.Compiler.FunctionalNative.AddSubCached.native.isBase address = true → values address = hom (baseValue address)) ∧
      (∀ definition ∈ Airbender.Compiler.FunctionalNative.AddSubCached.native.definitions, definition.Holds hom challenges values) ∧
      (∀ gate ∈ Airbender.Compiler.LookupNative.AddSubCached.native.gates, gate.Holds hom challenges gamma values) ∧
      (∀ gate ∈ Airbender.Compiler.ProductNative.AddSubCached.native.gates, gate.Holds hom challenges values) ∧
      (∀ index, baseValue (GKRAddress.BaseLayerWitness (Airbender.Compiler.TableNative.AddSubCached.native.multiplicityColumns.get index)) = counts index) ∧
      (∀ column ∈ native.columns, baseValue column.address = Airbender.Compiler.MaterializedNative.AddSubCached.native.model.value row column) ∧
      (∀ field ∈ Airbender.Compiler.HelperNative.AddSubCached.native.fields, (field.value (Airbender.Compiler.HelperNative.AddSubCached.native.sourceValues baseValue)).val < 524288) := by
  let initial := Airbender.Compiler.HelperValidityNative.AddSubCached.native.canonical sourceValue
  let extended := Airbender.Compiler.CounterFrameNative.AddSubCached.native.assigned initial counts
  have holds := Airbender.Compiler.CounterFrameNative.AddSubCached.native.source_preserved initial counts (Airbender.Compiler.HelperValidityNative.AddSubCached.native.source_holds sourceValue original clockValid)
  let full := Airbender.Compiler.FullArithmeticNative.AddSubCached.native.artifact.translation.extend extended
  let baseValue := Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.materialize full (Airbender.Compiler.MaterializedNative.AddSubCached.native.model.baseOracle row fallback)
  have arithmetic := Airbender.Compiler.FullArithmeticNative.AddSubCached.native.full_arithmetic_extends extended holds
  have baseArithmetic := WireBank.materialize_gates Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bankRoundTrip full
    (Airbender.Compiler.MaterializedNative.AddSubCached.native.model.baseOracle row fallback) Airbender.Compiler.FullArithmeticNative.AddSubCached.native.artifact.gates arithmetic.2
  have inputAgreement (wire) : baseValue (Airbender.Compiler.FullArithmeticNative.AddSubCached.native.inputBank.address wire) = extended wire :=
    WireBank.materialize_source_input Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank Airbender.Compiler.FullArithmeticNative.AddSubCached.native.inputBank Airbender.Compiler.FullArithmeticNative.AddSubCached.native.artifact.projection
      Airbender.Compiler.FullArithmeticNative.AddSubCached.native.inputCoordinates Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bankRoundTrip extended full arithmetic.1
      (Airbender.Compiler.MaterializedNative.AddSubCached.native.model.baseOracle row fallback) wire
  refine ⟨baseValue, Airbender.Compiler.FunctionalNative.AddSubCached.native.canonical hom challenges gamma baseValue, inputAgreement, baseArithmetic,
    Airbender.Compiler.FunctionalNative.AddSubCached.native.canonical_base hom challenges gamma baseValue,
    Airbender.Compiler.FunctionalNative.AddSubCached.native.canonical_affines hom challenges gamma baseValue baseArithmetic,
    Airbender.Compiler.FunctionalNative.AddSubCached.native.canonical_lookups hom challenges gamma baseValue,
    Airbender.Compiler.FunctionalNative.AddSubCached.native.canonical_products hom challenges gamma baseValue, ?_,
    native.materialized_cells Airbender.Compiler.MaterializedNative.AddSubCached.native.model row fallback full, ?_⟩
  · intro index
    have actual := inputAgreement (Airbender.Compiler.CounterFrameNative.AddSubCached.native.slots index)
    rw [Airbender.Compiler.CounterFrameNative.AddSubCached.native.slotsRoundTrip index] at actual
    exact actual.trans (Airbender.Compiler.CounterFrameNative.AddSubCached.native.counts_at initial counts index)
  · intro field member
    have same := Source.HelperField.transport_value field Airbender.Compiler.FullArithmeticNative.AddSubCached.native.helperPlacement Airbender.Compiler.HelperNative.AddSubCached.native.placement
      Airbender.Compiler.FullArithmeticNative.AddSubCached.native.inputBank Airbender.Compiler.MemoryNative.AddSubCached.native.bank (List.all_eq_true.mp Airbender.Compiler.HelperValidityNative.AddSubCached.native.transportChecked field member)
      extended baseValue inputAgreement
    change (field.value (Airbender.Compiler.HelperNative.AddSubCached.native.placement.project (baseValue ∘ Airbender.Compiler.MemoryNative.AddSubCached.native.bank.address))).val < 524288
    rw [same, Airbender.Compiler.CounterFrameNative.AddSubCached.native.helpers_preserved initial counts field member]
    exact Airbender.Compiler.HelperValidityNative.AddSubCached.native.helper_membership sourceValue primitives field member

end Airbender.Compiler.OracleFrameNative.AddSubCached
