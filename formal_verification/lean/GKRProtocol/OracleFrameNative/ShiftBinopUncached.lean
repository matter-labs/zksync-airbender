import GKRProtocol.OracleFrameImport
import GKRProtocol.CounterFrameNative.ShiftBinopUncached
import GKRProtocol.MaterializedNative.ShiftBinopUncached

namespace Airbender.Compiler.OracleFrameNative.ShiftBinopUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_lookup_oracle_frame native from "artifacts/compiler/shift-binop-uncached.json"
  base_model Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native typing Airbender.Compiler.ConsumerNative.ShiftBinopUncached.native.typing

theorem oracle_graph_extends {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (sourceValue : Fin 98 → Source.BaseField)
    (original : Satisfies (Airbender.Compiler.SourceContractNative.ShiftBinopUncached.native.originals.map Expression.polynomial) sourceValue)
    (clockValid : Source.clockContract Airbender.Compiler.SourceContractNative.ShiftBinopUncached.native.clock (Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.helperPlacement.memory.project sourceValue))
    (primitives : Airbender.Compiler.HelperValidityNative.ShiftBinopUncached.native.profile.ExecutionValid (Airbender.Compiler.HelperValidityNative.ShiftBinopUncached.native.execute.value (Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.helperPlacement.memory.project sourceValue))
      (Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.helperPlacement.memory.project sourceValue))
    (counts : Fin Airbender.Compiler.TableNative.ShiftBinopUncached.native.multiplicityColumns.length → Source.BaseField)
    (row : Fin Airbender.Compiler.MaterializedNative.ShiftBinopUncached.native.model.imported.data.length) (fallback : GKRAddress → Source.BaseField) :
    ∃ baseValue : GKRAddress → Source.BaseField, ∃ values : GKRAddress → R,
      (∀ wire, baseValue (Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.ShiftBinopUncached.native.assigned (Airbender.Compiler.HelperValidityNative.ShiftBinopUncached.native.canonical sourceValue) counts wire) ∧
      (∀ gate ∈ Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.artifact.gates, gate.expressionResidual (baseValue ∘ Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank.address) = 0) ∧
      (∀ address, Airbender.Compiler.FunctionalNative.ShiftBinopUncached.native.isBase address = true → values address = hom (baseValue address)) ∧
      (∀ definition ∈ Airbender.Compiler.FunctionalNative.ShiftBinopUncached.native.definitions, definition.Holds hom challenges values) ∧
      (∀ gate ∈ Airbender.Compiler.LookupNative.ShiftBinopUncached.native.gates, gate.Holds hom challenges gamma values) ∧
      (∀ gate ∈ Airbender.Compiler.ProductNative.ShiftBinopUncached.native.gates, gate.Holds hom challenges values) ∧
      (∀ index, baseValue (GKRAddress.BaseLayerWitness (Airbender.Compiler.TableNative.ShiftBinopUncached.native.multiplicityColumns.get index)) = counts index) ∧
      (∀ column ∈ native.columns, baseValue column.address = Airbender.Compiler.MaterializedNative.ShiftBinopUncached.native.model.value row column) ∧
      (∀ field ∈ Airbender.Compiler.HelperNative.ShiftBinopUncached.native.fields, (field.value (Airbender.Compiler.HelperNative.ShiftBinopUncached.native.sourceValues baseValue)).val < 524288) := by
  let initial := Airbender.Compiler.HelperValidityNative.ShiftBinopUncached.native.canonical sourceValue
  let extended := Airbender.Compiler.CounterFrameNative.ShiftBinopUncached.native.assigned initial counts
  have holds := Airbender.Compiler.CounterFrameNative.ShiftBinopUncached.native.source_preserved initial counts (Airbender.Compiler.HelperValidityNative.ShiftBinopUncached.native.source_holds sourceValue original clockValid)
  let full := Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.artifact.translation.extend extended
  let baseValue := Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank.materialize full (Airbender.Compiler.MaterializedNative.ShiftBinopUncached.native.model.baseOracle row fallback)
  have arithmetic := Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.full_arithmetic_extends extended holds
  have baseArithmetic := WireBank.materialize_gates Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bankRoundTrip full
    (Airbender.Compiler.MaterializedNative.ShiftBinopUncached.native.model.baseOracle row fallback) Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.artifact.gates arithmetic.2
  have inputAgreement (wire) : baseValue (Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.inputBank.address wire) = extended wire :=
    WireBank.materialize_source_input Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.inputBank Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.artifact.projection
      Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.inputCoordinates Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bankRoundTrip extended full arithmetic.1
      (Airbender.Compiler.MaterializedNative.ShiftBinopUncached.native.model.baseOracle row fallback) wire
  refine ⟨baseValue, Airbender.Compiler.FunctionalNative.ShiftBinopUncached.native.canonical hom challenges gamma baseValue, inputAgreement, baseArithmetic,
    Airbender.Compiler.FunctionalNative.ShiftBinopUncached.native.canonical_base hom challenges gamma baseValue,
    Airbender.Compiler.FunctionalNative.ShiftBinopUncached.native.canonical_affines hom challenges gamma baseValue baseArithmetic,
    Airbender.Compiler.FunctionalNative.ShiftBinopUncached.native.canonical_lookups hom challenges gamma baseValue,
    Airbender.Compiler.FunctionalNative.ShiftBinopUncached.native.canonical_products hom challenges gamma baseValue, ?_,
    native.materialized_cells Airbender.Compiler.MaterializedNative.ShiftBinopUncached.native.model row fallback full, ?_⟩
  · intro index
    have actual := inputAgreement (Airbender.Compiler.CounterFrameNative.ShiftBinopUncached.native.slots index)
    rw [Airbender.Compiler.CounterFrameNative.ShiftBinopUncached.native.slotsRoundTrip index] at actual
    exact actual.trans (Airbender.Compiler.CounterFrameNative.ShiftBinopUncached.native.counts_at initial counts index)
  · intro field member
    have same := Source.HelperField.transport_value field Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.helperPlacement Airbender.Compiler.HelperNative.ShiftBinopUncached.native.placement
      Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.inputBank Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.bank (List.all_eq_true.mp Airbender.Compiler.HelperValidityNative.ShiftBinopUncached.native.transportChecked field member)
      extended baseValue inputAgreement
    change (field.value (Airbender.Compiler.HelperNative.ShiftBinopUncached.native.placement.project (baseValue ∘ Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.bank.address))).val < 524288
    rw [same, Airbender.Compiler.CounterFrameNative.ShiftBinopUncached.native.helpers_preserved initial counts field member]
    exact Airbender.Compiler.HelperValidityNative.ShiftBinopUncached.native.helper_membership sourceValue primitives field member

end Airbender.Compiler.OracleFrameNative.ShiftBinopUncached
