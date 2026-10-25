import GKRProtocol.OracleFrameImport
import GKRProtocol.CounterFrameNative.JumpBranchCached
import GKRProtocol.MaterializedNative.JumpBranchCached

namespace Airbender.Compiler.OracleFrameNative.JumpBranchCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_lookup_oracle_frame native from "artifacts/compiler/jump-branch-cached.json"
  base_model Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native typing Airbender.Compiler.ConsumerNative.JumpBranchCached.native.typing

theorem oracle_graph_extends {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (sourceValue : Fin 55 → Source.BaseField)
    (original : Satisfies (Airbender.Compiler.SourceContractNative.JumpBranchCached.native.originals.map Expression.polynomial) sourceValue)
    (clockValid : Source.clockContract Airbender.Compiler.SourceContractNative.JumpBranchCached.native.clock (Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.helperPlacement.memory.project sourceValue))
    (primitives : Airbender.Compiler.HelperValidityNative.JumpBranchCached.native.profile.ExecutionValid (Airbender.Compiler.HelperValidityNative.JumpBranchCached.native.execute.value (Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.helperPlacement.memory.project sourceValue))
      (Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.helperPlacement.memory.project sourceValue))
    (counts : Fin Airbender.Compiler.TableNative.JumpBranchCached.native.multiplicityColumns.length → Source.BaseField)
    (row : Fin Airbender.Compiler.MaterializedNative.JumpBranchCached.native.model.imported.data.length) (fallback : GKRAddress → Source.BaseField) :
    ∃ baseValue : GKRAddress → Source.BaseField, ∃ values : GKRAddress → R,
      (∀ wire, baseValue (Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.JumpBranchCached.native.assigned (Airbender.Compiler.HelperValidityNative.JumpBranchCached.native.canonical sourceValue) counts wire) ∧
      (∀ gate ∈ Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.artifact.gates, gate.expressionResidual (baseValue ∘ Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.bank.address) = 0) ∧
      (∀ address, Airbender.Compiler.FunctionalNative.JumpBranchCached.native.isBase address = true → values address = hom (baseValue address)) ∧
      (∀ definition ∈ Airbender.Compiler.FunctionalNative.JumpBranchCached.native.definitions, definition.Holds hom challenges values) ∧
      (∀ gate ∈ Airbender.Compiler.LookupNative.JumpBranchCached.native.gates, gate.Holds hom challenges gamma values) ∧
      (∀ gate ∈ Airbender.Compiler.ProductNative.JumpBranchCached.native.gates, gate.Holds hom challenges values) ∧
      (∀ index, baseValue (GKRAddress.BaseLayerWitness (Airbender.Compiler.TableNative.JumpBranchCached.native.multiplicityColumns.get index)) = counts index) ∧
      (∀ column ∈ native.columns, baseValue column.address = Airbender.Compiler.MaterializedNative.JumpBranchCached.native.model.value row column) ∧
      (∀ field ∈ Airbender.Compiler.HelperNative.JumpBranchCached.native.fields, (field.value (Airbender.Compiler.HelperNative.JumpBranchCached.native.sourceValues baseValue)).val < 524288) := by
  let initial := Airbender.Compiler.HelperValidityNative.JumpBranchCached.native.canonical sourceValue
  let extended := Airbender.Compiler.CounterFrameNative.JumpBranchCached.native.assigned initial counts
  have holds := Airbender.Compiler.CounterFrameNative.JumpBranchCached.native.source_preserved initial counts (Airbender.Compiler.HelperValidityNative.JumpBranchCached.native.source_holds sourceValue original clockValid)
  let full := Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.artifact.translation.extend extended
  let baseValue := Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.bank.materialize full (Airbender.Compiler.MaterializedNative.JumpBranchCached.native.model.baseOracle row fallback)
  have arithmetic := Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.full_arithmetic_extends extended holds
  have baseArithmetic := WireBank.materialize_gates Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.bank Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.bankRoundTrip full
    (Airbender.Compiler.MaterializedNative.JumpBranchCached.native.model.baseOracle row fallback) Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.artifact.gates arithmetic.2
  have inputAgreement (wire) : baseValue (Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.inputBank.address wire) = extended wire :=
    WireBank.materialize_source_input Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.bank Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.inputBank Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.artifact.projection
      Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.inputCoordinates Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.bankRoundTrip extended full arithmetic.1
      (Airbender.Compiler.MaterializedNative.JumpBranchCached.native.model.baseOracle row fallback) wire
  refine ⟨baseValue, Airbender.Compiler.FunctionalNative.JumpBranchCached.native.canonical hom challenges gamma baseValue, inputAgreement, baseArithmetic,
    Airbender.Compiler.FunctionalNative.JumpBranchCached.native.canonical_base hom challenges gamma baseValue,
    Airbender.Compiler.FunctionalNative.JumpBranchCached.native.canonical_affines hom challenges gamma baseValue baseArithmetic,
    Airbender.Compiler.FunctionalNative.JumpBranchCached.native.canonical_lookups hom challenges gamma baseValue,
    Airbender.Compiler.FunctionalNative.JumpBranchCached.native.canonical_products hom challenges gamma baseValue, ?_,
    native.materialized_cells Airbender.Compiler.MaterializedNative.JumpBranchCached.native.model row fallback full, ?_⟩
  · intro index
    have actual := inputAgreement (Airbender.Compiler.CounterFrameNative.JumpBranchCached.native.slots index)
    rw [Airbender.Compiler.CounterFrameNative.JumpBranchCached.native.slotsRoundTrip index] at actual
    exact actual.trans (Airbender.Compiler.CounterFrameNative.JumpBranchCached.native.counts_at initial counts index)
  · intro field member
    have same := Source.HelperField.transport_value field Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.helperPlacement Airbender.Compiler.HelperNative.JumpBranchCached.native.placement
      Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.inputBank Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank (List.all_eq_true.mp Airbender.Compiler.HelperValidityNative.JumpBranchCached.native.transportChecked field member)
      extended baseValue inputAgreement
    change (field.value (Airbender.Compiler.HelperNative.JumpBranchCached.native.placement.project (baseValue ∘ Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank.address))).val < 524288
    rw [same, Airbender.Compiler.CounterFrameNative.JumpBranchCached.native.helpers_preserved initial counts field member]
    exact Airbender.Compiler.HelperValidityNative.JumpBranchCached.native.helper_membership sourceValue primitives field member

end Airbender.Compiler.OracleFrameNative.JumpBranchCached
