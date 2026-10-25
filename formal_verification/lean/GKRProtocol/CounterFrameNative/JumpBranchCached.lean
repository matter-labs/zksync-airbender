import GKRProtocol.CounterFrameImport
import GKRProtocol.HelperValidityNative.JumpBranchCached
import GKRProtocol.TableNative.JumpBranchCached

namespace Airbender.Compiler.CounterFrameNative.JumpBranchCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_counter_frame native from "artifacts/compiler/jump-branch-cached.json"
  base_model Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native
  table_model Airbender.Compiler.TableNative.JumpBranchCached.native
  helper_model Airbender.Compiler.HelperNative.JumpBranchCached.native inputs 55

theorem counter_graph_extends {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (sourceValue : Fin 55 → Source.BaseField)
    (original : Satisfies (Airbender.Compiler.SourceContractNative.JumpBranchCached.native.originals.map Expression.polynomial) sourceValue)
    (clockValid : Source.clockContract Airbender.Compiler.SourceContractNative.JumpBranchCached.native.clock (Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.helperPlacement.memory.project sourceValue))
    (primitives : Airbender.Compiler.HelperValidityNative.JumpBranchCached.native.profile.ExecutionValid (Airbender.Compiler.HelperValidityNative.JumpBranchCached.native.execute.value (Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.helperPlacement.memory.project sourceValue))
      (Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.helperPlacement.memory.project sourceValue))
    (counts : Fin Airbender.Compiler.TableNative.JumpBranchCached.native.multiplicityColumns.length → Source.BaseField)
    (fallback : GKRAddress → Source.BaseField) :
    ∃ baseValue : GKRAddress → Source.BaseField, ∃ values : GKRAddress → R,
      (∀ wire, baseValue (Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.inputBank.address wire) = native.assigned (Airbender.Compiler.HelperValidityNative.JumpBranchCached.native.canonical sourceValue) counts wire) ∧
      (∀ gate ∈ Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.artifact.gates, gate.expressionResidual (baseValue ∘ Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.bank.address) = 0) ∧
      (∀ address, Airbender.Compiler.FunctionalNative.JumpBranchCached.native.isBase address = true → values address = hom (baseValue address)) ∧
      (∀ definition ∈ Airbender.Compiler.FunctionalNative.JumpBranchCached.native.definitions, definition.Holds hom challenges values) ∧
      (∀ gate ∈ Airbender.Compiler.LookupNative.JumpBranchCached.native.gates, gate.Holds hom challenges gamma values) ∧
      (∀ gate ∈ Airbender.Compiler.ProductNative.JumpBranchCached.native.gates, gate.Holds hom challenges values) ∧
      (∀ index, baseValue (GKRAddress.BaseLayerWitness (Airbender.Compiler.TableNative.JumpBranchCached.native.multiplicityColumns.get index)) = counts index) ∧
      (∀ field ∈ Airbender.Compiler.HelperNative.JumpBranchCached.native.fields, (field.value (Airbender.Compiler.HelperNative.JumpBranchCached.native.sourceValues baseValue)).val < 524288) := by
  let initial := Airbender.Compiler.HelperValidityNative.JumpBranchCached.native.canonical sourceValue
  let extended := native.assigned initial counts
  have holds := native.source_preserved initial counts (Airbender.Compiler.HelperValidityNative.JumpBranchCached.native.source_holds sourceValue original clockValid)
  obtain ⟨baseValue, values, inputAgreement, arithmetic, baseLaw, affine, lookups, products⟩ :=
    Airbender.Compiler.FunctionalNative.JumpBranchCached.native.full_graph_extends hom challenges gamma extended holds fallback
  refine ⟨baseValue, values, inputAgreement, arithmetic, baseLaw, affine, lookups, products, ?_, ?_⟩
  · intro index
    have actual := inputAgreement (native.slots index)
    rw [native.slotsRoundTrip index] at actual
    exact actual.trans (native.counts_at initial counts index)
  · intro field member
    have same := Source.HelperField.transport_value field Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.helperPlacement Airbender.Compiler.HelperNative.JumpBranchCached.native.placement
      Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.inputBank Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank (List.all_eq_true.mp Airbender.Compiler.HelperValidityNative.JumpBranchCached.native.transportChecked field member)
      extended baseValue inputAgreement
    change (field.value (Airbender.Compiler.HelperNative.JumpBranchCached.native.placement.project (baseValue ∘ Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank.address))).val < 524288
    rw [same, native.helpers_preserved initial counts field member]
    exact Airbender.Compiler.HelperValidityNative.JumpBranchCached.native.helper_membership sourceValue primitives field member

end Airbender.Compiler.CounterFrameNative.JumpBranchCached
