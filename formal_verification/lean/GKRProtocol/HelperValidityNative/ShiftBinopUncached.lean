import GKRProtocol.HelperValidityImport
import GKRProtocol.HistoryErasureNative.ShiftBinopUncached
import GKRProtocol.HelperNative.ShiftBinopUncached

namespace Airbender.Compiler.HelperValidityNative.ShiftBinopUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_helper_validity native from "artifacts/compiler/shift-binop-uncached-source.json"
  base_model Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native
  source_model Airbender.Compiler.SourceContractNative.ShiftBinopUncached.native
  history_model Airbender.Compiler.HistoryErasureNative.ShiftBinopUncached.native
  helper_model Airbender.Compiler.HelperNative.ShiftBinopUncached.native
  memory_model Airbender.Compiler.MemoryNative.ShiftBinopUncached.native inputs 98

theorem helper_graph_extends {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (sourceValue : Fin 98 → Source.BaseField)
    (original : Satisfies (Airbender.Compiler.SourceContractNative.ShiftBinopUncached.native.originals.map Expression.polynomial) sourceValue)
    (clockValid : Source.clockContract Airbender.Compiler.SourceContractNative.ShiftBinopUncached.native.clock (Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.helperPlacement.memory.project sourceValue))
    (primitives : native.profile.ExecutionValid (native.execute.value (Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.helperPlacement.memory.project sourceValue))
      (Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.helperPlacement.memory.project sourceValue)) (fallback : GKRAddress → Source.BaseField) :
    ∃ baseValue : GKRAddress → Source.BaseField, ∃ values : GKRAddress → R,
      (∀ wire, baseValue (Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.inputBank.address wire) = native.canonical sourceValue wire) ∧
      (∀ gate ∈ Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.artifact.gates, gate.expressionResidual (baseValue ∘ Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank.address) = 0) ∧
      (∀ address, Airbender.Compiler.FunctionalNative.ShiftBinopUncached.native.isBase address = true → values address = hom (baseValue address)) ∧
      (∀ definition ∈ Airbender.Compiler.FunctionalNative.ShiftBinopUncached.native.definitions, definition.Holds hom challenges values) ∧
      (∀ gate ∈ Airbender.Compiler.LookupNative.ShiftBinopUncached.native.gates, gate.Holds hom challenges gamma values) ∧
      (∀ gate ∈ Airbender.Compiler.ProductNative.ShiftBinopUncached.native.gates, gate.Holds hom challenges values) ∧
      (∀ field ∈ Airbender.Compiler.HelperNative.ShiftBinopUncached.native.fields, (field.value (Airbender.Compiler.HelperNative.ShiftBinopUncached.native.sourceValues baseValue)).val < 524288) := by
  obtain ⟨baseValue, values, inputAgreement, arithmetic, baseLaw, affine, lookups, products⟩ :=
    Airbender.Compiler.FunctionalNative.ShiftBinopUncached.native.full_graph_extends hom challenges gamma (native.canonical sourceValue)
      (native.source_holds sourceValue original clockValid) fallback
  exact ⟨baseValue, values, inputAgreement, arithmetic, baseLaw, affine, lookups, products,
    native.native_helper_membership sourceValue primitives baseValue inputAgreement⟩

end Airbender.Compiler.HelperValidityNative.ShiftBinopUncached
