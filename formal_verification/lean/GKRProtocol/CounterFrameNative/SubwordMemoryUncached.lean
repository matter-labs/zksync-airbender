import GKRProtocol.CounterFrameImport
import GKRProtocol.HelperValidityNative.SubwordMemoryUncached
import GKRProtocol.TableNative.SubwordMemoryUncached

namespace Airbender.Compiler.CounterFrameNative.SubwordMemoryUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_counter_frame native from "artifacts/compiler/subword-memory-uncached.json"
  base_model Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native
  table_model Airbender.Compiler.TableNative.SubwordMemoryUncached.native
  helper_model Airbender.Compiler.HelperNative.SubwordMemoryUncached.native inputs 68

theorem counter_graph_extends {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (sourceValue : Fin 68 → Source.BaseField)
    (original : Satisfies (Airbender.Compiler.SourceContractNative.SubwordMemoryUncached.native.originals.map Expression.polynomial) sourceValue)
    (clockValid : Source.clockContract Airbender.Compiler.SourceContractNative.SubwordMemoryUncached.native.clock (Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.helperPlacement.memory.project sourceValue))
    (primitives : Airbender.Compiler.HelperValidityNative.SubwordMemoryUncached.native.profile.ExecutionValid (Airbender.Compiler.HelperValidityNative.SubwordMemoryUncached.native.execute.value (Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.helperPlacement.memory.project sourceValue))
      (Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.helperPlacement.memory.project sourceValue))
    (counts : Fin Airbender.Compiler.TableNative.SubwordMemoryUncached.native.multiplicityColumns.length → Source.BaseField)
    (fallback : GKRAddress → Source.BaseField) :
    ∃ baseValue : GKRAddress → Source.BaseField, ∃ values : GKRAddress → R,
      (∀ wire, baseValue (Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.inputBank.address wire) = native.assigned (Airbender.Compiler.HelperValidityNative.SubwordMemoryUncached.native.canonical sourceValue) counts wire) ∧
      (∀ gate ∈ Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.artifact.gates, gate.expressionResidual (baseValue ∘ Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.bank.address) = 0) ∧
      (∀ address, Airbender.Compiler.FunctionalNative.SubwordMemoryUncached.native.isBase address = true → values address = hom (baseValue address)) ∧
      (∀ definition ∈ Airbender.Compiler.FunctionalNative.SubwordMemoryUncached.native.definitions, definition.Holds hom challenges values) ∧
      (∀ gate ∈ Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.gates, gate.Holds hom challenges gamma values) ∧
      (∀ gate ∈ Airbender.Compiler.ProductNative.SubwordMemoryUncached.native.gates, gate.Holds hom challenges values) ∧
      (∀ index, baseValue (GKRAddress.BaseLayerWitness (Airbender.Compiler.TableNative.SubwordMemoryUncached.native.multiplicityColumns.get index)) = counts index) ∧
      (∀ field ∈ Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.fields, (field.value (Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.sourceValues baseValue)).val < 524288) := by
  let initial := Airbender.Compiler.HelperValidityNative.SubwordMemoryUncached.native.canonical sourceValue
  let extended := native.assigned initial counts
  have holds := native.source_preserved initial counts (Airbender.Compiler.HelperValidityNative.SubwordMemoryUncached.native.source_holds sourceValue original clockValid)
  obtain ⟨baseValue, values, inputAgreement, arithmetic, baseLaw, affine, lookups, products⟩ :=
    Airbender.Compiler.FunctionalNative.SubwordMemoryUncached.native.full_graph_extends hom challenges gamma extended holds fallback
  refine ⟨baseValue, values, inputAgreement, arithmetic, baseLaw, affine, lookups, products, ?_, ?_⟩
  · intro index
    have actual := inputAgreement (native.slots index)
    rw [native.slotsRoundTrip index] at actual
    exact actual.trans (native.counts_at initial counts index)
  · intro field member
    have same := Source.HelperField.transport_value field Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.helperPlacement Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.placement
      Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.inputBank Airbender.Compiler.MemoryNative.SubwordMemoryUncached.native.bank (List.all_eq_true.mp Airbender.Compiler.HelperValidityNative.SubwordMemoryUncached.native.transportChecked field member)
      extended baseValue inputAgreement
    change (field.value (Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.placement.project (baseValue ∘ Airbender.Compiler.MemoryNative.SubwordMemoryUncached.native.bank.address))).val < 524288
    rw [same, native.helpers_preserved initial counts field member]
    exact Airbender.Compiler.HelperValidityNative.SubwordMemoryUncached.native.helper_membership sourceValue primitives field member

end Airbender.Compiler.CounterFrameNative.SubwordMemoryUncached
