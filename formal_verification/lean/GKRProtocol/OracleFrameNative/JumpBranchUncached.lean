import GKRProtocol.OracleFrameImport
import GKRProtocol.CounterFrameNative.JumpBranchUncached
import GKRProtocol.MaterializedNative.JumpBranchUncached

namespace Airbender.Compiler.OracleFrameNative.JumpBranchUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_lookup_oracle_frame native from "artifacts/compiler/jump-branch-uncached.json"
  base_model Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native typing Airbender.Compiler.ConsumerNative.JumpBranchUncached.native.typing

theorem oracle_graph_extends {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (sourceValue : Fin 55 → Source.BaseField)
    (original : Satisfies (Airbender.Compiler.SourceContractNative.JumpBranchUncached.native.originals.map Expression.polynomial) sourceValue)
    (clockValid : Source.clockContract Airbender.Compiler.SourceContractNative.JumpBranchUncached.native.clock (Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.helperPlacement.memory.project sourceValue))
    (primitives : Airbender.Compiler.HelperValidityNative.JumpBranchUncached.native.profile.ExecutionValid (Airbender.Compiler.HelperValidityNative.JumpBranchUncached.native.execute.value (Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.helperPlacement.memory.project sourceValue))
      (Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.helperPlacement.memory.project sourceValue))
    (counts : Fin Airbender.Compiler.TableNative.JumpBranchUncached.native.multiplicityColumns.length → Source.BaseField)
    (row : Fin Airbender.Compiler.MaterializedNative.JumpBranchUncached.native.model.imported.data.length) (fallback : GKRAddress → Source.BaseField) :
    ∃ baseValue : GKRAddress → Source.BaseField, ∃ values : GKRAddress → R,
      (∀ wire, baseValue (Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.JumpBranchUncached.native.assigned (Airbender.Compiler.HelperValidityNative.JumpBranchUncached.native.canonical sourceValue) counts wire) ∧
      (∀ gate ∈ Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.artifact.gates, gate.expressionResidual (baseValue ∘ Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.bank.address) = 0) ∧
      (∀ address, Airbender.Compiler.FunctionalNative.JumpBranchUncached.native.isBase address = true → values address = hom (baseValue address)) ∧
      (∀ definition ∈ Airbender.Compiler.FunctionalNative.JumpBranchUncached.native.definitions, definition.Holds hom challenges values) ∧
      (∀ gate ∈ Airbender.Compiler.LookupNative.JumpBranchUncached.native.gates, gate.Holds hom challenges gamma values) ∧
      (∀ gate ∈ Airbender.Compiler.ProductNative.JumpBranchUncached.native.gates, gate.Holds hom challenges values) ∧
      (∀ index, baseValue (GKRAddress.BaseLayerWitness (Airbender.Compiler.TableNative.JumpBranchUncached.native.multiplicityColumns.get index)) = counts index) ∧
      (∀ column ∈ native.columns, baseValue column.address = Airbender.Compiler.MaterializedNative.JumpBranchUncached.native.model.value row column) ∧
      (∀ field ∈ Airbender.Compiler.HelperNative.JumpBranchUncached.native.fields, (field.value (Airbender.Compiler.HelperNative.JumpBranchUncached.native.sourceValues baseValue)).val < 524288) := by
  let initial := Airbender.Compiler.HelperValidityNative.JumpBranchUncached.native.canonical sourceValue
  let extended := Airbender.Compiler.CounterFrameNative.JumpBranchUncached.native.assigned initial counts
  have holds := Airbender.Compiler.CounterFrameNative.JumpBranchUncached.native.source_preserved initial counts (Airbender.Compiler.HelperValidityNative.JumpBranchUncached.native.source_holds sourceValue original clockValid)
  let full := Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.artifact.translation.extend extended
  let baseValue := Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.bank.materialize full (Airbender.Compiler.MaterializedNative.JumpBranchUncached.native.model.baseOracle row fallback)
  have arithmetic := Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.full_arithmetic_extends extended holds
  have baseArithmetic := WireBank.materialize_gates Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.bank Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.bankRoundTrip full
    (Airbender.Compiler.MaterializedNative.JumpBranchUncached.native.model.baseOracle row fallback) Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.artifact.gates arithmetic.2
  have inputAgreement (wire) : baseValue (Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.inputBank.address wire) = extended wire :=
    WireBank.materialize_source_input Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.bank Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.inputBank Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.artifact.projection
      Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.inputCoordinates Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.bankRoundTrip extended full arithmetic.1
      (Airbender.Compiler.MaterializedNative.JumpBranchUncached.native.model.baseOracle row fallback) wire
  refine ⟨baseValue, Airbender.Compiler.FunctionalNative.JumpBranchUncached.native.canonical hom challenges gamma baseValue, inputAgreement, baseArithmetic,
    Airbender.Compiler.FunctionalNative.JumpBranchUncached.native.canonical_base hom challenges gamma baseValue,
    Airbender.Compiler.FunctionalNative.JumpBranchUncached.native.canonical_affines hom challenges gamma baseValue baseArithmetic,
    Airbender.Compiler.FunctionalNative.JumpBranchUncached.native.canonical_lookups hom challenges gamma baseValue,
    Airbender.Compiler.FunctionalNative.JumpBranchUncached.native.canonical_products hom challenges gamma baseValue, ?_,
    native.materialized_cells Airbender.Compiler.MaterializedNative.JumpBranchUncached.native.model row fallback full, ?_⟩
  · intro index
    have actual := inputAgreement (Airbender.Compiler.CounterFrameNative.JumpBranchUncached.native.slots index)
    rw [Airbender.Compiler.CounterFrameNative.JumpBranchUncached.native.slotsRoundTrip index] at actual
    exact actual.trans (Airbender.Compiler.CounterFrameNative.JumpBranchUncached.native.counts_at initial counts index)
  · intro field member
    have same := Source.HelperField.transport_value field Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.helperPlacement Airbender.Compiler.HelperNative.JumpBranchUncached.native.placement
      Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.inputBank Airbender.Compiler.MemoryNative.JumpBranchUncached.native.bank (List.all_eq_true.mp Airbender.Compiler.HelperValidityNative.JumpBranchUncached.native.transportChecked field member)
      extended baseValue inputAgreement
    change (field.value (Airbender.Compiler.HelperNative.JumpBranchUncached.native.placement.project (baseValue ∘ Airbender.Compiler.MemoryNative.JumpBranchUncached.native.bank.address))).val < 524288
    rw [same, Airbender.Compiler.CounterFrameNative.JumpBranchUncached.native.helpers_preserved initial counts field member]
    exact Airbender.Compiler.HelperValidityNative.JumpBranchUncached.native.helper_membership sourceValue primitives field member

end Airbender.Compiler.OracleFrameNative.JumpBranchUncached
