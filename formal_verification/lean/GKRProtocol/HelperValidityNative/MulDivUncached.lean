import GKRProtocol.HelperValidityImport
import GKRProtocol.HistoryErasureNative.MulDivUncached
import GKRProtocol.HelperNative.MulDivUncached

namespace Airbender.Compiler.HelperValidityNative.MulDivUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_helper_validity native from "artifacts/compiler/mul-div-uncached-source.json"
  base_model Airbender.Compiler.FullArithmeticNative.MulDivUncached.native
  source_model Airbender.Compiler.SourceContractNative.MulDivUncached.native
  history_model Airbender.Compiler.HistoryErasureNative.MulDivUncached.native
  helper_model Airbender.Compiler.HelperNative.MulDivUncached.native
  memory_model Airbender.Compiler.MemoryNative.MulDivUncached.native inputs 71

theorem helper_graph_extends {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (sourceValue : Fin 71 → Source.BaseField)
    (original : Satisfies (Airbender.Compiler.SourceContractNative.MulDivUncached.native.originals.map Expression.polynomial) sourceValue)
    (clockValid : Source.clockContract Airbender.Compiler.SourceContractNative.MulDivUncached.native.clock (Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.helperPlacement.memory.project sourceValue))
    (primitives : native.profile.ExecutionValid (native.execute.value (Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.helperPlacement.memory.project sourceValue))
      (Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.helperPlacement.memory.project sourceValue)) (fallback : GKRAddress → Source.BaseField) :
    ∃ baseValue : GKRAddress → Source.BaseField, ∃ values : GKRAddress → R,
      (∀ wire, baseValue (Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.inputBank.address wire) = native.canonical sourceValue wire) ∧
      (∀ gate ∈ Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.artifact.gates, gate.expressionResidual (baseValue ∘ Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.bank.address) = 0) ∧
      (∀ address, Airbender.Compiler.FunctionalNative.MulDivUncached.native.isBase address = true → values address = hom (baseValue address)) ∧
      (∀ definition ∈ Airbender.Compiler.FunctionalNative.MulDivUncached.native.definitions, definition.Holds hom challenges values) ∧
      (∀ gate ∈ Airbender.Compiler.LookupNative.MulDivUncached.native.gates, gate.Holds hom challenges gamma values) ∧
      (∀ gate ∈ Airbender.Compiler.ProductNative.MulDivUncached.native.gates, gate.Holds hom challenges values) ∧
      (∀ field ∈ Airbender.Compiler.HelperNative.MulDivUncached.native.fields, (field.value (Airbender.Compiler.HelperNative.MulDivUncached.native.sourceValues baseValue)).val < 524288) := by
  obtain ⟨baseValue, values, inputAgreement, arithmetic, baseLaw, affine, lookups, products⟩ :=
    Airbender.Compiler.FunctionalNative.MulDivUncached.native.full_graph_extends hom challenges gamma (native.canonical sourceValue)
      (native.source_holds sourceValue original clockValid) fallback
  exact ⟨baseValue, values, inputAgreement, arithmetic, baseLaw, affine, lookups, products,
    native.native_helper_membership sourceValue primitives baseValue inputAgreement⟩

end Airbender.Compiler.HelperValidityNative.MulDivUncached
