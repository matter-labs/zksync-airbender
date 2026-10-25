import GKRProtocol.HelperValidityImport
import GKRProtocol.HistoryErasureNative.KeccakCached
import GKRProtocol.HelperNative.KeccakCached

namespace Airbender.Compiler.HelperValidityNative.KeccakCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_helper_validity native from "artifacts/compiler/keccak-cached-source.json"
  base_model Airbender.Compiler.FullArithmeticNative.KeccakCached.native
  source_model Airbender.Compiler.SourceContractNative.KeccakCached.native
  history_model Airbender.Compiler.HistoryErasureNative.KeccakCached.native
  helper_model Airbender.Compiler.HelperNative.KeccakCached.native
  memory_model Airbender.Compiler.MemoryNative.KeccakCached.native inputs 267

theorem helper_graph_extends {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (sourceValue : Fin 267 → Source.BaseField)
    (original : Satisfies (Airbender.Compiler.SourceContractNative.KeccakCached.native.originals.map Expression.polynomial) sourceValue)
    (clockValid : Source.clockContract Airbender.Compiler.SourceContractNative.KeccakCached.native.clock (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.helperPlacement.memory.project sourceValue))
    (primitives : native.profile.ExecutionValid (native.execute.value (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.helperPlacement.memory.project sourceValue))
      (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.helperPlacement.memory.project sourceValue)) (fallback : GKRAddress → Source.BaseField) :
    ∃ baseValue : GKRAddress → Source.BaseField, ∃ values : GKRAddress → R,
      (∀ wire, baseValue (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.inputBank.address wire) = native.canonical sourceValue wire) ∧
      (∀ gate ∈ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.artifact.gates, gate.expressionResidual (baseValue ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address) = 0) ∧
      (∀ address, Airbender.Compiler.FunctionalNative.KeccakCached.native.isBase address = true → values address = hom (baseValue address)) ∧
      (∀ definition ∈ Airbender.Compiler.FunctionalNative.KeccakCached.native.definitions, definition.Holds hom challenges values) ∧
      (∀ gate ∈ Airbender.Compiler.LookupNative.KeccakCached.native.gates, gate.Holds hom challenges gamma values) ∧
      (∀ gate ∈ Airbender.Compiler.ProductNative.KeccakCached.native.gates, gate.Holds hom challenges values) ∧
      (∀ field ∈ Airbender.Compiler.HelperNative.KeccakCached.native.fields, (field.value (Airbender.Compiler.HelperNative.KeccakCached.native.sourceValues baseValue)).val < 524288) := by
  obtain ⟨baseValue, values, inputAgreement, arithmetic, baseLaw, affine, lookups, products⟩ :=
    Airbender.Compiler.FunctionalNative.KeccakCached.native.full_graph_extends hom challenges gamma (native.canonical sourceValue)
      (native.source_holds sourceValue original clockValid) fallback
  exact ⟨baseValue, values, inputAgreement, arithmetic, baseLaw, affine, lookups, products,
    native.native_helper_membership sourceValue primitives baseValue inputAgreement⟩

end Airbender.Compiler.HelperValidityNative.KeccakCached
