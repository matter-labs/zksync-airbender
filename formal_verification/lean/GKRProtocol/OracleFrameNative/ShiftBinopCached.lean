import GKRProtocol.OracleFrameImport
import GKRProtocol.CounterFrameNative.ShiftBinopCached
import GKRProtocol.MaterializedNative.ShiftBinopCached

namespace Airbender.Compiler.OracleFrameNative.ShiftBinopCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_lookup_oracle_frame native from "artifacts/compiler/shift-binop-cached.json"
  base_model Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native typing Airbender.Compiler.ConsumerNative.ShiftBinopCached.native.typing

theorem oracle_graph_extends {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (sourceValue : Fin 98 → Source.BaseField)
    (original : Satisfies (Airbender.Compiler.SourceContractNative.ShiftBinopCached.native.originals.map Expression.polynomial) sourceValue)
    (clockValid : Source.clockContract Airbender.Compiler.SourceContractNative.ShiftBinopCached.native.clock (Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.helperPlacement.memory.project sourceValue))
    (primitives : Airbender.Compiler.HelperValidityNative.ShiftBinopCached.native.profile.ExecutionValid (Airbender.Compiler.HelperValidityNative.ShiftBinopCached.native.execute.value (Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.helperPlacement.memory.project sourceValue))
      (Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.helperPlacement.memory.project sourceValue))
    (counts : Fin Airbender.Compiler.TableNative.ShiftBinopCached.native.multiplicityColumns.length → Source.BaseField)
    (row : Fin Airbender.Compiler.MaterializedNative.ShiftBinopCached.native.model.imported.data.length) (fallback : GKRAddress → Source.BaseField) :
    ∃ baseValue : GKRAddress → Source.BaseField, ∃ values : GKRAddress → R,
      (∀ wire, baseValue (Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.ShiftBinopCached.native.assigned (Airbender.Compiler.HelperValidityNative.ShiftBinopCached.native.canonical sourceValue) counts wire) ∧
      (∀ gate ∈ Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.artifact.gates, gate.expressionResidual (baseValue ∘ Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.bank.address) = 0) ∧
      (∀ address, Airbender.Compiler.FunctionalNative.ShiftBinopCached.native.isBase address = true → values address = hom (baseValue address)) ∧
      (∀ definition ∈ Airbender.Compiler.FunctionalNative.ShiftBinopCached.native.definitions, definition.Holds hom challenges values) ∧
      (∀ gate ∈ Airbender.Compiler.LookupNative.ShiftBinopCached.native.gates, gate.Holds hom challenges gamma values) ∧
      (∀ gate ∈ Airbender.Compiler.ProductNative.ShiftBinopCached.native.gates, gate.Holds hom challenges values) ∧
      (∀ index, baseValue (GKRAddress.BaseLayerWitness (Airbender.Compiler.TableNative.ShiftBinopCached.native.multiplicityColumns.get index)) = counts index) ∧
      (∀ column ∈ native.columns, baseValue column.address = Airbender.Compiler.MaterializedNative.ShiftBinopCached.native.model.value row column) ∧
      (∀ field ∈ Airbender.Compiler.HelperNative.ShiftBinopCached.native.fields, (field.value (Airbender.Compiler.HelperNative.ShiftBinopCached.native.sourceValues baseValue)).val < 524288) := by
  let initial := Airbender.Compiler.HelperValidityNative.ShiftBinopCached.native.canonical sourceValue
  let extended := Airbender.Compiler.CounterFrameNative.ShiftBinopCached.native.assigned initial counts
  have holds := Airbender.Compiler.CounterFrameNative.ShiftBinopCached.native.source_preserved initial counts (Airbender.Compiler.HelperValidityNative.ShiftBinopCached.native.source_holds sourceValue original clockValid)
  let full := Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.artifact.translation.extend extended
  let baseValue := Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.bank.materialize full (Airbender.Compiler.MaterializedNative.ShiftBinopCached.native.model.baseOracle row fallback)
  have arithmetic := Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.full_arithmetic_extends extended holds
  have baseArithmetic := WireBank.materialize_gates Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.bank Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.bankRoundTrip full
    (Airbender.Compiler.MaterializedNative.ShiftBinopCached.native.model.baseOracle row fallback) Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.artifact.gates arithmetic.2
  have inputAgreement (wire) : baseValue (Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.inputBank.address wire) = extended wire :=
    WireBank.materialize_source_input Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.bank Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.inputBank Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.artifact.projection
      Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.inputCoordinates Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.bankRoundTrip extended full arithmetic.1
      (Airbender.Compiler.MaterializedNative.ShiftBinopCached.native.model.baseOracle row fallback) wire
  refine ⟨baseValue, Airbender.Compiler.FunctionalNative.ShiftBinopCached.native.canonical hom challenges gamma baseValue, inputAgreement, baseArithmetic,
    Airbender.Compiler.FunctionalNative.ShiftBinopCached.native.canonical_base hom challenges gamma baseValue,
    Airbender.Compiler.FunctionalNative.ShiftBinopCached.native.canonical_affines hom challenges gamma baseValue baseArithmetic,
    Airbender.Compiler.FunctionalNative.ShiftBinopCached.native.canonical_lookups hom challenges gamma baseValue,
    Airbender.Compiler.FunctionalNative.ShiftBinopCached.native.canonical_products hom challenges gamma baseValue, ?_,
    native.materialized_cells Airbender.Compiler.MaterializedNative.ShiftBinopCached.native.model row fallback full, ?_⟩
  · intro index
    have actual := inputAgreement (Airbender.Compiler.CounterFrameNative.ShiftBinopCached.native.slots index)
    rw [Airbender.Compiler.CounterFrameNative.ShiftBinopCached.native.slotsRoundTrip index] at actual
    exact actual.trans (Airbender.Compiler.CounterFrameNative.ShiftBinopCached.native.counts_at initial counts index)
  · intro field member
    have same := Source.HelperField.transport_value field Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.helperPlacement Airbender.Compiler.HelperNative.ShiftBinopCached.native.placement
      Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.inputBank Airbender.Compiler.MemoryNative.ShiftBinopCached.native.bank (List.all_eq_true.mp Airbender.Compiler.HelperValidityNative.ShiftBinopCached.native.transportChecked field member)
      extended baseValue inputAgreement
    change (field.value (Airbender.Compiler.HelperNative.ShiftBinopCached.native.placement.project (baseValue ∘ Airbender.Compiler.MemoryNative.ShiftBinopCached.native.bank.address))).val < 524288
    rw [same, Airbender.Compiler.CounterFrameNative.ShiftBinopCached.native.helpers_preserved initial counts field member]
    exact Airbender.Compiler.HelperValidityNative.ShiftBinopCached.native.helper_membership sourceValue primitives field member

end Airbender.Compiler.OracleFrameNative.ShiftBinopCached
