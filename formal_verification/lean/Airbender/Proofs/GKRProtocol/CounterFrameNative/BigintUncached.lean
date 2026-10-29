import Airbender.Import.GKRProtocol.CounterFrameImport
import Airbender.Proofs.GKRProtocol.HelperValidityNative.BigintUncached
import Airbender.Proofs.GKRProtocol.TableNative.BigintUncached

namespace Airbender.Compiler.CounterFrameNative.BigintUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_counter_frame native from "artifacts/compiler/bigint-uncached.json"
  base_model Airbender.Compiler.FullArithmeticNative.BigintUncached.native
  table_model Airbender.Compiler.TableNative.BigintUncached.native
  helper_model Airbender.Compiler.HelperNative.BigintUncached.native inputs 276

theorem counter_graph_extends {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (sourceValue : Fin 276 → Source.BaseField)
    (original : Satisfies (Airbender.Compiler.SourceContractNative.BigintUncached.native.originals.map Expression.polynomial) sourceValue)
    (clockValid : Source.clockContract Airbender.Compiler.SourceContractNative.BigintUncached.native.clock (Airbender.Compiler.FullArithmeticNative.BigintUncached.native.helperPlacement.memory.project sourceValue))
    (primitives : Airbender.Compiler.HelperValidityNative.BigintUncached.native.profile.ExecutionValid (Airbender.Compiler.HelperValidityNative.BigintUncached.native.execute.value (Airbender.Compiler.FullArithmeticNative.BigintUncached.native.helperPlacement.memory.project sourceValue))
      (Airbender.Compiler.FullArithmeticNative.BigintUncached.native.helperPlacement.memory.project sourceValue))
    (counts : Fin Airbender.Compiler.TableNative.BigintUncached.native.multiplicityColumns.length → Source.BaseField)
    (fallback : GKRAddress → Source.BaseField) :
    ∃ baseValue : GKRAddress → Source.BaseField, ∃ values : GKRAddress → R,
      (∀ wire, baseValue (Airbender.Compiler.FullArithmeticNative.BigintUncached.native.inputBank.address wire) = native.assigned (Airbender.Compiler.HelperValidityNative.BigintUncached.native.canonical sourceValue) counts wire) ∧
      (∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.artifact.gates, gate.expressionResidual (baseValue ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank.address) = 0) ∧
      (∀ address, Airbender.Compiler.FunctionalNative.BigintUncached.native.isBase address = true → values address = hom (baseValue address)) ∧
      (∀ definition ∈ Airbender.Compiler.FunctionalNative.BigintUncached.native.definitions, definition.Holds hom challenges values) ∧
      (∀ gate ∈ Airbender.Compiler.LookupNative.BigintUncached.native.gates, gate.Holds hom challenges gamma values) ∧
      (∀ gate ∈ Airbender.Compiler.ProductNative.BigintUncached.native.gates, gate.Holds hom challenges values) ∧
      (∀ index, baseValue (GKRAddress.BaseLayerWitness (Airbender.Compiler.TableNative.BigintUncached.native.multiplicityColumns.get index)) = counts index) ∧
      (∀ field ∈ Airbender.Compiler.HelperNative.BigintUncached.native.fields, (field.value (Airbender.Compiler.HelperNative.BigintUncached.native.sourceValues baseValue)).val < 524288) := by
  let initial := Airbender.Compiler.HelperValidityNative.BigintUncached.native.canonical sourceValue
  let extended := native.assigned initial counts
  have holds := native.source_preserved initial counts (Airbender.Compiler.HelperValidityNative.BigintUncached.native.source_holds sourceValue original clockValid)
  obtain ⟨baseValue, values, inputAgreement, arithmetic, baseLaw, affine, lookups, products⟩ :=
    Airbender.Compiler.FunctionalNative.BigintUncached.native.full_graph_extends hom challenges gamma extended holds fallback
  refine ⟨baseValue, values, inputAgreement, arithmetic, baseLaw, affine, lookups, products, ?_, ?_⟩
  · intro index
    have actual := inputAgreement (native.slots index)
    rw [native.slotsRoundTrip index] at actual
    exact actual.trans (native.counts_at initial counts index)
  · intro field member
    have same := Source.HelperField.transport_value field Airbender.Compiler.FullArithmeticNative.BigintUncached.native.helperPlacement Airbender.Compiler.HelperNative.BigintUncached.native.placement
      Airbender.Compiler.FullArithmeticNative.BigintUncached.native.inputBank Airbender.Compiler.MemoryNative.BigintUncached.native.bank (List.all_eq_true.mp Airbender.Compiler.HelperValidityNative.BigintUncached.native.transportChecked field member)
      extended baseValue inputAgreement
    change (field.value (Airbender.Compiler.HelperNative.BigintUncached.native.placement.project (baseValue ∘ Airbender.Compiler.MemoryNative.BigintUncached.native.bank.address))).val < 524288
    rw [same, native.helpers_preserved initial counts field member]
    exact Airbender.Compiler.HelperValidityNative.BigintUncached.native.helper_membership sourceValue primitives field member

end Airbender.Compiler.CounterFrameNative.BigintUncached
