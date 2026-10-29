import Airbender.Import.GKRProtocol.HelperValidityImport
import Airbender.Proofs.GKRProtocol.HistoryErasureNative.UnifiedCached
import Airbender.Proofs.GKRProtocol.HelperNative.UnifiedCached

namespace Airbender.Compiler.HelperValidityNative.UnifiedCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_helper_validity native from "artifacts/compiler/unified-cached-source.json"
  base_model Airbender.Compiler.FullArithmeticNative.UnifiedCached.native
  source_model Airbender.Compiler.SourceContractNative.UnifiedCached.native
  history_model Airbender.Compiler.HistoryErasureNative.UnifiedCached.native
  helper_model Airbender.Compiler.HelperNative.UnifiedCached.native
  memory_model Airbender.Compiler.MemoryNative.UnifiedCached.native inputs 137

theorem helper_graph_extends {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (sourceValue : Fin 137 → Source.BaseField)
    (original : Satisfies (Airbender.Compiler.SourceContractNative.UnifiedCached.native.originals.map Expression.polynomial) sourceValue)
    (clockValid : Source.clockContract Airbender.Compiler.SourceContractNative.UnifiedCached.native.clock (Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.helperPlacement.memory.project sourceValue))
    (primitives : native.profile.ExecutionValid (native.execute.value (Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.helperPlacement.memory.project sourceValue))
      (Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.helperPlacement.memory.project sourceValue)) (fallback : GKRAddress → Source.BaseField) :
    ∃ baseValue : GKRAddress → Source.BaseField, ∃ values : GKRAddress → R,
      (∀ wire, baseValue (Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.inputBank.address wire) = native.canonical sourceValue wire) ∧
      (∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (baseValue ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0) ∧
      (∀ address, Airbender.Compiler.FunctionalNative.UnifiedCached.native.isBase address = true → values address = hom (baseValue address)) ∧
      (∀ definition ∈ Airbender.Compiler.FunctionalNative.UnifiedCached.native.definitions, definition.Holds hom challenges values) ∧
      (∀ gate ∈ Airbender.Compiler.LookupNative.UnifiedCached.native.gates, gate.Holds hom challenges gamma values) ∧
      (∀ gate ∈ Airbender.Compiler.ProductNative.UnifiedCached.native.gates, gate.Holds hom challenges values) ∧
      (∀ field ∈ Airbender.Compiler.HelperNative.UnifiedCached.native.fields, (field.value (Airbender.Compiler.HelperNative.UnifiedCached.native.sourceValues baseValue)).val < 524288) := by
  obtain ⟨baseValue, values, inputAgreement, arithmetic, baseLaw, affine, lookups, products⟩ :=
    Airbender.Compiler.FunctionalNative.UnifiedCached.native.full_graph_extends hom challenges gamma (native.canonical sourceValue)
      (native.source_holds sourceValue original clockValid) fallback
  exact ⟨baseValue, values, inputAgreement, arithmetic, baseLaw, affine, lookups, products,
    native.native_helper_membership sourceValue primitives baseValue inputAgreement⟩

end Airbender.Compiler.HelperValidityNative.UnifiedCached
