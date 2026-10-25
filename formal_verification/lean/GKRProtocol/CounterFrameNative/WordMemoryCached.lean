import GKRProtocol.CounterFrameImport
import GKRProtocol.HelperValidityNative.WordMemoryCached
import GKRProtocol.TableNative.WordMemoryCached

namespace Airbender.Compiler.CounterFrameNative.WordMemoryCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_counter_frame native from "artifacts/compiler/word-memory-cached.json"
  base_model Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native
  table_model Airbender.Compiler.TableNative.WordMemoryCached.native
  helper_model Airbender.Compiler.HelperNative.WordMemoryCached.native inputs 52

theorem counter_graph_extends {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (sourceValue : Fin 52 → Source.BaseField)
    (original : Satisfies (Airbender.Compiler.SourceContractNative.WordMemoryCached.native.originals.map Expression.polynomial) sourceValue)
    (clockValid : Source.clockContract Airbender.Compiler.SourceContractNative.WordMemoryCached.native.clock (Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.helperPlacement.memory.project sourceValue))
    (primitives : Airbender.Compiler.HelperValidityNative.WordMemoryCached.native.profile.ExecutionValid (Airbender.Compiler.HelperValidityNative.WordMemoryCached.native.execute.value (Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.helperPlacement.memory.project sourceValue))
      (Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.helperPlacement.memory.project sourceValue))
    (counts : Fin Airbender.Compiler.TableNative.WordMemoryCached.native.multiplicityColumns.length → Source.BaseField)
    (fallback : GKRAddress → Source.BaseField) :
    ∃ baseValue : GKRAddress → Source.BaseField, ∃ values : GKRAddress → R,
      (∀ wire, baseValue (Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.inputBank.address wire) = native.assigned (Airbender.Compiler.HelperValidityNative.WordMemoryCached.native.canonical sourceValue) counts wire) ∧
      (∀ gate ∈ Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.artifact.gates, gate.expressionResidual (baseValue ∘ Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.bank.address) = 0) ∧
      (∀ address, Airbender.Compiler.FunctionalNative.WordMemoryCached.native.isBase address = true → values address = hom (baseValue address)) ∧
      (∀ definition ∈ Airbender.Compiler.FunctionalNative.WordMemoryCached.native.definitions, definition.Holds hom challenges values) ∧
      (∀ gate ∈ Airbender.Compiler.LookupNative.WordMemoryCached.native.gates, gate.Holds hom challenges gamma values) ∧
      (∀ gate ∈ Airbender.Compiler.ProductNative.WordMemoryCached.native.gates, gate.Holds hom challenges values) ∧
      (∀ index, baseValue (GKRAddress.BaseLayerWitness (Airbender.Compiler.TableNative.WordMemoryCached.native.multiplicityColumns.get index)) = counts index) ∧
      (∀ field ∈ Airbender.Compiler.HelperNative.WordMemoryCached.native.fields, (field.value (Airbender.Compiler.HelperNative.WordMemoryCached.native.sourceValues baseValue)).val < 524288) := by
  let initial := Airbender.Compiler.HelperValidityNative.WordMemoryCached.native.canonical sourceValue
  let extended := native.assigned initial counts
  have holds := native.source_preserved initial counts (Airbender.Compiler.HelperValidityNative.WordMemoryCached.native.source_holds sourceValue original clockValid)
  obtain ⟨baseValue, values, inputAgreement, arithmetic, baseLaw, affine, lookups, products⟩ :=
    Airbender.Compiler.FunctionalNative.WordMemoryCached.native.full_graph_extends hom challenges gamma extended holds fallback
  refine ⟨baseValue, values, inputAgreement, arithmetic, baseLaw, affine, lookups, products, ?_, ?_⟩
  · intro index
    have actual := inputAgreement (native.slots index)
    rw [native.slotsRoundTrip index] at actual
    exact actual.trans (native.counts_at initial counts index)
  · intro field member
    have same := Source.HelperField.transport_value field Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.helperPlacement Airbender.Compiler.HelperNative.WordMemoryCached.native.placement
      Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.inputBank Airbender.Compiler.MemoryNative.WordMemoryCached.native.bank (List.all_eq_true.mp Airbender.Compiler.HelperValidityNative.WordMemoryCached.native.transportChecked field member)
      extended baseValue inputAgreement
    change (field.value (Airbender.Compiler.HelperNative.WordMemoryCached.native.placement.project (baseValue ∘ Airbender.Compiler.MemoryNative.WordMemoryCached.native.bank.address))).val < 524288
    rw [same, native.helpers_preserved initial counts field member]
    exact Airbender.Compiler.HelperValidityNative.WordMemoryCached.native.helper_membership sourceValue primitives field member

end Airbender.Compiler.CounterFrameNative.WordMemoryCached
