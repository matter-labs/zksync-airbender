import Airbender.Import.GKRProtocol.OracleFrameImport
import Airbender.Proofs.GKRProtocol.CounterFrameNative.MulDivCached
import Airbender.Proofs.GKRProtocol.MaterializedNative.MulDivCached

namespace Airbender.Compiler.OracleFrameNative.MulDivCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_lookup_oracle_frame native from "artifacts/compiler/mul-div-cached.json"
  base_model Airbender.Compiler.FullArithmeticNative.MulDivCached.native typing Airbender.Compiler.ConsumerNative.MulDivCached.native.typing

theorem oracle_graph_extends {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (sourceValue : Fin 71 → Source.BaseField)
    (original : Satisfies (Airbender.Compiler.SourceContractNative.MulDivCached.native.originals.map Expression.polynomial) sourceValue)
    (clockValid : Source.clockContract Airbender.Compiler.SourceContractNative.MulDivCached.native.clock (Airbender.Compiler.FullArithmeticNative.MulDivCached.native.helperPlacement.memory.project sourceValue))
    (primitives : Airbender.Compiler.HelperValidityNative.MulDivCached.native.profile.ExecutionValid (Airbender.Compiler.HelperValidityNative.MulDivCached.native.execute.value (Airbender.Compiler.FullArithmeticNative.MulDivCached.native.helperPlacement.memory.project sourceValue))
      (Airbender.Compiler.FullArithmeticNative.MulDivCached.native.helperPlacement.memory.project sourceValue))
    (counts : Fin Airbender.Compiler.TableNative.MulDivCached.native.multiplicityColumns.length → Source.BaseField)
    (row : Fin Airbender.Compiler.MaterializedNative.MulDivCached.native.model.imported.data.length) (fallback : GKRAddress → Source.BaseField) :
    ∃ baseValue : GKRAddress → Source.BaseField, ∃ values : GKRAddress → R,
      (∀ wire, baseValue (Airbender.Compiler.FullArithmeticNative.MulDivCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.MulDivCached.native.assigned (Airbender.Compiler.HelperValidityNative.MulDivCached.native.canonical sourceValue) counts wire) ∧
      (∀ gate ∈ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.artifact.gates, gate.expressionResidual (baseValue ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) = 0) ∧
      (∀ address, Airbender.Compiler.FunctionalNative.MulDivCached.native.isBase address = true → values address = hom (baseValue address)) ∧
      (∀ definition ∈ Airbender.Compiler.FunctionalNative.MulDivCached.native.definitions, definition.Holds hom challenges values) ∧
      (∀ gate ∈ Airbender.Compiler.LookupNative.MulDivCached.native.gates, gate.Holds hom challenges gamma values) ∧
      (∀ gate ∈ Airbender.Compiler.ProductNative.MulDivCached.native.gates, gate.Holds hom challenges values) ∧
      (∀ index, baseValue (GKRAddress.BaseLayerWitness (Airbender.Compiler.TableNative.MulDivCached.native.multiplicityColumns.get index)) = counts index) ∧
      (∀ column ∈ native.columns, baseValue column.address = Airbender.Compiler.MaterializedNative.MulDivCached.native.model.value row column) ∧
      (∀ field ∈ Airbender.Compiler.HelperNative.MulDivCached.native.fields, (field.value (Airbender.Compiler.HelperNative.MulDivCached.native.sourceValues baseValue)).val < 524288) := by
  let initial := Airbender.Compiler.HelperValidityNative.MulDivCached.native.canonical sourceValue
  let extended := Airbender.Compiler.CounterFrameNative.MulDivCached.native.assigned initial counts
  have holds := Airbender.Compiler.CounterFrameNative.MulDivCached.native.source_preserved initial counts (Airbender.Compiler.HelperValidityNative.MulDivCached.native.source_holds sourceValue original clockValid)
  let full := Airbender.Compiler.FullArithmeticNative.MulDivCached.native.artifact.translation.extend extended
  let baseValue := Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.materialize full (Airbender.Compiler.MaterializedNative.MulDivCached.native.model.baseOracle row fallback)
  have arithmetic := Airbender.Compiler.FullArithmeticNative.MulDivCached.native.full_arithmetic_extends extended holds
  have baseArithmetic := WireBank.materialize_gates Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bankRoundTrip full
    (Airbender.Compiler.MaterializedNative.MulDivCached.native.model.baseOracle row fallback) Airbender.Compiler.FullArithmeticNative.MulDivCached.native.artifact.gates arithmetic.2
  have inputAgreement (wire) : baseValue (Airbender.Compiler.FullArithmeticNative.MulDivCached.native.inputBank.address wire) = extended wire :=
    WireBank.materialize_source_input Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank Airbender.Compiler.FullArithmeticNative.MulDivCached.native.inputBank Airbender.Compiler.FullArithmeticNative.MulDivCached.native.artifact.projection
      Airbender.Compiler.FullArithmeticNative.MulDivCached.native.inputCoordinates Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bankRoundTrip extended full arithmetic.1
      (Airbender.Compiler.MaterializedNative.MulDivCached.native.model.baseOracle row fallback) wire
  refine ⟨baseValue, Airbender.Compiler.FunctionalNative.MulDivCached.native.canonical hom challenges gamma baseValue, inputAgreement, baseArithmetic,
    Airbender.Compiler.FunctionalNative.MulDivCached.native.canonical_base hom challenges gamma baseValue,
    Airbender.Compiler.FunctionalNative.MulDivCached.native.canonical_affines hom challenges gamma baseValue baseArithmetic,
    Airbender.Compiler.FunctionalNative.MulDivCached.native.canonical_lookups hom challenges gamma baseValue,
    Airbender.Compiler.FunctionalNative.MulDivCached.native.canonical_products hom challenges gamma baseValue, ?_,
    native.materialized_cells Airbender.Compiler.MaterializedNative.MulDivCached.native.model row fallback full, ?_⟩
  · intro index
    have actual := inputAgreement (Airbender.Compiler.CounterFrameNative.MulDivCached.native.slots index)
    rw [Airbender.Compiler.CounterFrameNative.MulDivCached.native.slotsRoundTrip index] at actual
    exact actual.trans (Airbender.Compiler.CounterFrameNative.MulDivCached.native.counts_at initial counts index)
  · intro field member
    have same := Source.HelperField.transport_value field Airbender.Compiler.FullArithmeticNative.MulDivCached.native.helperPlacement Airbender.Compiler.HelperNative.MulDivCached.native.placement
      Airbender.Compiler.FullArithmeticNative.MulDivCached.native.inputBank Airbender.Compiler.MemoryNative.MulDivCached.native.bank (List.all_eq_true.mp Airbender.Compiler.HelperValidityNative.MulDivCached.native.transportChecked field member)
      extended baseValue inputAgreement
    change (field.value (Airbender.Compiler.HelperNative.MulDivCached.native.placement.project (baseValue ∘ Airbender.Compiler.MemoryNative.MulDivCached.native.bank.address))).val < 524288
    rw [same, Airbender.Compiler.CounterFrameNative.MulDivCached.native.helpers_preserved initial counts field member]
    exact Airbender.Compiler.HelperValidityNative.MulDivCached.native.helper_membership sourceValue primitives field member

end Airbender.Compiler.OracleFrameNative.MulDivCached
