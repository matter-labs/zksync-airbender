import Airbender.Import.GKRProtocol.CounterFrameImport
import Airbender.Proofs.GKRProtocol.HelperValidityNative.UnifiedCached
import Airbender.Proofs.GKRProtocol.TableNative.UnifiedCached

namespace Airbender.Compiler.CounterFrameNative.UnifiedCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_counter_frame native from "artifacts/compiler/unified-cached.json"
  base_model Airbender.Compiler.FullArithmeticNative.UnifiedCached.native
  table_model Airbender.Compiler.TableNative.UnifiedCached.native
  helper_model Airbender.Compiler.HelperNative.UnifiedCached.native inputs 137

theorem counter_graph_extends {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (sourceValue : Fin 137 → Source.BaseField)
    (original : Satisfies (Airbender.Compiler.SourceContractNative.UnifiedCached.native.originals.map Expression.polynomial) sourceValue)
    (clockValid : Source.clockContract Airbender.Compiler.SourceContractNative.UnifiedCached.native.clock (Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.helperPlacement.memory.project sourceValue))
    (primitives : Airbender.Compiler.HelperValidityNative.UnifiedCached.native.profile.ExecutionValid (Airbender.Compiler.HelperValidityNative.UnifiedCached.native.execute.value (Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.helperPlacement.memory.project sourceValue))
      (Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.helperPlacement.memory.project sourceValue))
    (counts : Fin Airbender.Compiler.TableNative.UnifiedCached.native.multiplicityColumns.length → Source.BaseField)
    (fallback : GKRAddress → Source.BaseField) :
    ∃ baseValue : GKRAddress → Source.BaseField, ∃ values : GKRAddress → R,
      (∀ wire, baseValue (Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.inputBank.address wire) = native.assigned (Airbender.Compiler.HelperValidityNative.UnifiedCached.native.canonical sourceValue) counts wire) ∧
      (∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (baseValue ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0) ∧
      (∀ address, Airbender.Compiler.FunctionalNative.UnifiedCached.native.isBase address = true → values address = hom (baseValue address)) ∧
      (∀ definition ∈ Airbender.Compiler.FunctionalNative.UnifiedCached.native.definitions, definition.Holds hom challenges values) ∧
      (∀ gate ∈ Airbender.Compiler.LookupNative.UnifiedCached.native.gates, gate.Holds hom challenges gamma values) ∧
      (∀ gate ∈ Airbender.Compiler.ProductNative.UnifiedCached.native.gates, gate.Holds hom challenges values) ∧
      (∀ index, baseValue (GKRAddress.BaseLayerWitness (Airbender.Compiler.TableNative.UnifiedCached.native.multiplicityColumns.get index)) = counts index) ∧
      (∀ field ∈ Airbender.Compiler.HelperNative.UnifiedCached.native.fields, (field.value (Airbender.Compiler.HelperNative.UnifiedCached.native.sourceValues baseValue)).val < 524288) := by
  let initial := Airbender.Compiler.HelperValidityNative.UnifiedCached.native.canonical sourceValue
  let extended := native.assigned initial counts
  have holds := native.source_preserved initial counts (Airbender.Compiler.HelperValidityNative.UnifiedCached.native.source_holds sourceValue original clockValid)
  obtain ⟨baseValue, values, inputAgreement, arithmetic, baseLaw, affine, lookups, products⟩ :=
    Airbender.Compiler.FunctionalNative.UnifiedCached.native.full_graph_extends hom challenges gamma extended holds fallback
  refine ⟨baseValue, values, inputAgreement, arithmetic, baseLaw, affine, lookups, products, ?_, ?_⟩
  · intro index
    have actual := inputAgreement (native.slots index)
    rw [native.slotsRoundTrip index] at actual
    exact actual.trans (native.counts_at initial counts index)
  · intro field member
    have same := Source.HelperField.transport_value field Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.helperPlacement Airbender.Compiler.HelperNative.UnifiedCached.native.placement
      Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.inputBank Airbender.Compiler.MemoryNative.UnifiedCached.native.bank (List.all_eq_true.mp Airbender.Compiler.HelperValidityNative.UnifiedCached.native.transportChecked field member)
      extended baseValue inputAgreement
    change (field.value (Airbender.Compiler.HelperNative.UnifiedCached.native.placement.project (baseValue ∘ Airbender.Compiler.MemoryNative.UnifiedCached.native.bank.address))).val < 524288
    rw [same, native.helpers_preserved initial counts field member]
    exact Airbender.Compiler.HelperValidityNative.UnifiedCached.native.helper_membership sourceValue primitives field member

end Airbender.Compiler.CounterFrameNative.UnifiedCached
