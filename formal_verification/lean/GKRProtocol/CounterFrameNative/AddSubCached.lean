import GKRProtocol.CounterFrameImport
import GKRProtocol.HelperValidityNative.AddSubCached
import GKRProtocol.TableNative.AddSubCached

namespace Airbender.Compiler.CounterFrameNative.AddSubCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_counter_frame native from "artifacts/compiler/add-sub-cached.json"
  base_model Airbender.Compiler.FullArithmeticNative.AddSubCached.native
  table_model Airbender.Compiler.TableNative.AddSubCached.native
  helper_model Airbender.Compiler.HelperNative.AddSubCached.native inputs 48

theorem counter_graph_extends {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (sourceValue : Fin 48 → Source.BaseField)
    (original : Satisfies (Airbender.Compiler.SourceContractNative.AddSubCached.native.originals.map Expression.polynomial) sourceValue)
    (clockValid : Source.clockContract Airbender.Compiler.SourceContractNative.AddSubCached.native.clock (Airbender.Compiler.FullArithmeticNative.AddSubCached.native.helperPlacement.memory.project sourceValue))
    (primitives : Airbender.Compiler.HelperValidityNative.AddSubCached.native.profile.ExecutionValid (Airbender.Compiler.HelperValidityNative.AddSubCached.native.execute.value (Airbender.Compiler.FullArithmeticNative.AddSubCached.native.helperPlacement.memory.project sourceValue))
      (Airbender.Compiler.FullArithmeticNative.AddSubCached.native.helperPlacement.memory.project sourceValue))
    (counts : Fin Airbender.Compiler.TableNative.AddSubCached.native.multiplicityColumns.length → Source.BaseField)
    (fallback : GKRAddress → Source.BaseField) :
    ∃ baseValue : GKRAddress → Source.BaseField, ∃ values : GKRAddress → R,
      (∀ wire, baseValue (Airbender.Compiler.FullArithmeticNative.AddSubCached.native.inputBank.address wire) = native.assigned (Airbender.Compiler.HelperValidityNative.AddSubCached.native.canonical sourceValue) counts wire) ∧
      (∀ gate ∈ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.artifact.gates, gate.expressionResidual (baseValue ∘ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address) = 0) ∧
      (∀ address, Airbender.Compiler.FunctionalNative.AddSubCached.native.isBase address = true → values address = hom (baseValue address)) ∧
      (∀ definition ∈ Airbender.Compiler.FunctionalNative.AddSubCached.native.definitions, definition.Holds hom challenges values) ∧
      (∀ gate ∈ Airbender.Compiler.LookupNative.AddSubCached.native.gates, gate.Holds hom challenges gamma values) ∧
      (∀ gate ∈ Airbender.Compiler.ProductNative.AddSubCached.native.gates, gate.Holds hom challenges values) ∧
      (∀ index, baseValue (GKRAddress.BaseLayerWitness (Airbender.Compiler.TableNative.AddSubCached.native.multiplicityColumns.get index)) = counts index) ∧
      (∀ field ∈ Airbender.Compiler.HelperNative.AddSubCached.native.fields, (field.value (Airbender.Compiler.HelperNative.AddSubCached.native.sourceValues baseValue)).val < 524288) := by
  let initial := Airbender.Compiler.HelperValidityNative.AddSubCached.native.canonical sourceValue
  let extended := native.assigned initial counts
  have holds := native.source_preserved initial counts (Airbender.Compiler.HelperValidityNative.AddSubCached.native.source_holds sourceValue original clockValid)
  obtain ⟨baseValue, values, inputAgreement, arithmetic, baseLaw, affine, lookups, products⟩ :=
    Airbender.Compiler.FunctionalNative.AddSubCached.native.full_graph_extends hom challenges gamma extended holds fallback
  refine ⟨baseValue, values, inputAgreement, arithmetic, baseLaw, affine, lookups, products, ?_, ?_⟩
  · intro index
    have actual := inputAgreement (native.slots index)
    rw [native.slotsRoundTrip index] at actual
    exact actual.trans (native.counts_at initial counts index)
  · intro field member
    have same := Source.HelperField.transport_value field Airbender.Compiler.FullArithmeticNative.AddSubCached.native.helperPlacement Airbender.Compiler.HelperNative.AddSubCached.native.placement
      Airbender.Compiler.FullArithmeticNative.AddSubCached.native.inputBank Airbender.Compiler.MemoryNative.AddSubCached.native.bank (List.all_eq_true.mp Airbender.Compiler.HelperValidityNative.AddSubCached.native.transportChecked field member)
      extended baseValue inputAgreement
    change (field.value (Airbender.Compiler.HelperNative.AddSubCached.native.placement.project (baseValue ∘ Airbender.Compiler.MemoryNative.AddSubCached.native.bank.address))).val < 524288
    rw [same, native.helpers_preserved initial counts field member]
    exact Airbender.Compiler.HelperValidityNative.AddSubCached.native.helper_membership sourceValue primitives field member

end Airbender.Compiler.CounterFrameNative.AddSubCached
