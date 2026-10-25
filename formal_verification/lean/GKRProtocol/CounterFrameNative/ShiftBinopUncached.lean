import GKRProtocol.CounterFrameImport
import GKRProtocol.HelperValidityNative.ShiftBinopUncached
import GKRProtocol.TableNative.ShiftBinopUncached

namespace Airbender.Compiler.CounterFrameNative.ShiftBinopUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_counter_frame native from "artifacts/compiler/shift-binop-uncached.json"
  base_model Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native
  table_model Airbender.Compiler.TableNative.ShiftBinopUncached.native
  helper_model Airbender.Compiler.HelperNative.ShiftBinopUncached.native inputs 98

theorem counter_graph_extends {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (sourceValue : Fin 98 → Source.BaseField)
    (original : Satisfies (Airbender.Compiler.SourceContractNative.ShiftBinopUncached.native.originals.map Expression.polynomial) sourceValue)
    (clockValid : Source.clockContract Airbender.Compiler.SourceContractNative.ShiftBinopUncached.native.clock (Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.helperPlacement.memory.project sourceValue))
    (primitives : Airbender.Compiler.HelperValidityNative.ShiftBinopUncached.native.profile.ExecutionValid (Airbender.Compiler.HelperValidityNative.ShiftBinopUncached.native.execute.value (Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.helperPlacement.memory.project sourceValue))
      (Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.helperPlacement.memory.project sourceValue))
    (counts : Fin Airbender.Compiler.TableNative.ShiftBinopUncached.native.multiplicityColumns.length → Source.BaseField)
    (fallback : GKRAddress → Source.BaseField) :
    ∃ baseValue : GKRAddress → Source.BaseField, ∃ values : GKRAddress → R,
      (∀ wire, baseValue (Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.inputBank.address wire) = native.assigned (Airbender.Compiler.HelperValidityNative.ShiftBinopUncached.native.canonical sourceValue) counts wire) ∧
      (∀ gate ∈ Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.artifact.gates, gate.expressionResidual (baseValue ∘ Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank.address) = 0) ∧
      (∀ address, Airbender.Compiler.FunctionalNative.ShiftBinopUncached.native.isBase address = true → values address = hom (baseValue address)) ∧
      (∀ definition ∈ Airbender.Compiler.FunctionalNative.ShiftBinopUncached.native.definitions, definition.Holds hom challenges values) ∧
      (∀ gate ∈ Airbender.Compiler.LookupNative.ShiftBinopUncached.native.gates, gate.Holds hom challenges gamma values) ∧
      (∀ gate ∈ Airbender.Compiler.ProductNative.ShiftBinopUncached.native.gates, gate.Holds hom challenges values) ∧
      (∀ index, baseValue (GKRAddress.BaseLayerWitness (Airbender.Compiler.TableNative.ShiftBinopUncached.native.multiplicityColumns.get index)) = counts index) ∧
      (∀ field ∈ Airbender.Compiler.HelperNative.ShiftBinopUncached.native.fields, (field.value (Airbender.Compiler.HelperNative.ShiftBinopUncached.native.sourceValues baseValue)).val < 524288) := by
  let initial := Airbender.Compiler.HelperValidityNative.ShiftBinopUncached.native.canonical sourceValue
  let extended := native.assigned initial counts
  have holds := native.source_preserved initial counts (Airbender.Compiler.HelperValidityNative.ShiftBinopUncached.native.source_holds sourceValue original clockValid)
  obtain ⟨baseValue, values, inputAgreement, arithmetic, baseLaw, affine, lookups, products⟩ :=
    Airbender.Compiler.FunctionalNative.ShiftBinopUncached.native.full_graph_extends hom challenges gamma extended holds fallback
  refine ⟨baseValue, values, inputAgreement, arithmetic, baseLaw, affine, lookups, products, ?_, ?_⟩
  · intro index
    have actual := inputAgreement (native.slots index)
    rw [native.slotsRoundTrip index] at actual
    exact actual.trans (native.counts_at initial counts index)
  · intro field member
    have same := Source.HelperField.transport_value field Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.helperPlacement Airbender.Compiler.HelperNative.ShiftBinopUncached.native.placement
      Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.inputBank Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.bank (List.all_eq_true.mp Airbender.Compiler.HelperValidityNative.ShiftBinopUncached.native.transportChecked field member)
      extended baseValue inputAgreement
    change (field.value (Airbender.Compiler.HelperNative.ShiftBinopUncached.native.placement.project (baseValue ∘ Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.bank.address))).val < 524288
    rw [same, native.helpers_preserved initial counts field member]
    exact Airbender.Compiler.HelperValidityNative.ShiftBinopUncached.native.helper_membership sourceValue primitives field member

end Airbender.Compiler.CounterFrameNative.ShiftBinopUncached
