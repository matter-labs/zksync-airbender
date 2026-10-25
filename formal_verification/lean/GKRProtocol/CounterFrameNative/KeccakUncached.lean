import GKRProtocol.CounterFrameImport
import GKRProtocol.HelperValidityNative.KeccakUncached
import GKRProtocol.TableNative.KeccakUncached

namespace Airbender.Compiler.CounterFrameNative.KeccakUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_counter_frame native from "artifacts/compiler/keccak-uncached.json"
  base_model Airbender.Compiler.FullArithmeticNative.KeccakUncached.native
  table_model Airbender.Compiler.TableNative.KeccakUncached.native
  helper_model Airbender.Compiler.HelperNative.KeccakUncached.native inputs 267

theorem counter_graph_extends {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (sourceValue : Fin 267 → Source.BaseField)
    (original : Satisfies (Airbender.Compiler.SourceContractNative.KeccakUncached.native.originals.map Expression.polynomial) sourceValue)
    (clockValid : Source.clockContract Airbender.Compiler.SourceContractNative.KeccakUncached.native.clock (Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.helperPlacement.memory.project sourceValue))
    (primitives : Airbender.Compiler.HelperValidityNative.KeccakUncached.native.profile.ExecutionValid (Airbender.Compiler.HelperValidityNative.KeccakUncached.native.execute.value (Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.helperPlacement.memory.project sourceValue))
      (Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.helperPlacement.memory.project sourceValue))
    (counts : Fin Airbender.Compiler.TableNative.KeccakUncached.native.multiplicityColumns.length → Source.BaseField)
    (fallback : GKRAddress → Source.BaseField) :
    ∃ baseValue : GKRAddress → Source.BaseField, ∃ values : GKRAddress → R,
      (∀ wire, baseValue (Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.inputBank.address wire) = native.assigned (Airbender.Compiler.HelperValidityNative.KeccakUncached.native.canonical sourceValue) counts wire) ∧
      (∀ gate ∈ Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.artifact.gates, gate.expressionResidual (baseValue ∘ Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank.address) = 0) ∧
      (∀ address, Airbender.Compiler.FunctionalNative.KeccakUncached.native.isBase address = true → values address = hom (baseValue address)) ∧
      (∀ definition ∈ Airbender.Compiler.FunctionalNative.KeccakUncached.native.definitions, definition.Holds hom challenges values) ∧
      (∀ gate ∈ Airbender.Compiler.LookupNative.KeccakUncached.native.gates, gate.Holds hom challenges gamma values) ∧
      (∀ gate ∈ Airbender.Compiler.ProductNative.KeccakUncached.native.gates, gate.Holds hom challenges values) ∧
      (∀ index, baseValue (GKRAddress.BaseLayerWitness (Airbender.Compiler.TableNative.KeccakUncached.native.multiplicityColumns.get index)) = counts index) ∧
      (∀ field ∈ Airbender.Compiler.HelperNative.KeccakUncached.native.fields, (field.value (Airbender.Compiler.HelperNative.KeccakUncached.native.sourceValues baseValue)).val < 524288) := by
  let initial := Airbender.Compiler.HelperValidityNative.KeccakUncached.native.canonical sourceValue
  let extended := native.assigned initial counts
  have holds := native.source_preserved initial counts (Airbender.Compiler.HelperValidityNative.KeccakUncached.native.source_holds sourceValue original clockValid)
  obtain ⟨baseValue, values, inputAgreement, arithmetic, baseLaw, affine, lookups, products⟩ :=
    Airbender.Compiler.FunctionalNative.KeccakUncached.native.full_graph_extends hom challenges gamma extended holds fallback
  refine ⟨baseValue, values, inputAgreement, arithmetic, baseLaw, affine, lookups, products, ?_, ?_⟩
  · intro index
    have actual := inputAgreement (native.slots index)
    rw [native.slotsRoundTrip index] at actual
    exact actual.trans (native.counts_at initial counts index)
  · intro field member
    have same := Source.HelperField.transport_value field Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.helperPlacement Airbender.Compiler.HelperNative.KeccakUncached.native.placement
      Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.inputBank Airbender.Compiler.MemoryNative.KeccakUncached.native.bank (List.all_eq_true.mp Airbender.Compiler.HelperValidityNative.KeccakUncached.native.transportChecked field member)
      extended baseValue inputAgreement
    change (field.value (Airbender.Compiler.HelperNative.KeccakUncached.native.placement.project (baseValue ∘ Airbender.Compiler.MemoryNative.KeccakUncached.native.bank.address))).val < 524288
    rw [same, native.helpers_preserved initial counts field member]
    exact Airbender.Compiler.HelperValidityNative.KeccakUncached.native.helper_membership sourceValue primitives field member

end Airbender.Compiler.CounterFrameNative.KeccakUncached
