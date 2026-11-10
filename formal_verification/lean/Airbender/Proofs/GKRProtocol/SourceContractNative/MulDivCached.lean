import Airbender.Import.GKRProtocol.SourceContractImport
import Airbender.Proofs.GKRProtocol.FunctionalNative.MulDivCached

namespace Airbender.Compiler.SourceContractNative.MulDivCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_compiler_source_contract native from "artifacts/compiler/mul-div-cached.json"
  source "artifacts/compiler/mul-div-cached-source.json" base_model Airbender.Compiler.FullArithmeticNative.MulDivCached.native inputs 71

theorem source_contract_graph_extends {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (sourceValue : Fin Airbender.Compiler.FullArithmeticNative.MulDivCached.native.inputs.length → Source.BaseField)
    (original : Satisfies (native.originals.map Expression.polynomial) sourceValue)
    (clockValid : Source.clockContract native.clock (Airbender.Compiler.FullArithmeticNative.MulDivCached.native.helperPlacement.memory.project sourceValue))
    (fallback : GKRAddress → Source.BaseField) :
    ∃ sourceExtended : Fin Airbender.Compiler.FullArithmeticNative.MulDivCached.native.inputs.length → Source.BaseField,
      (∀ index, (∀ borrow, native.slots borrow ≠ index) → sourceExtended index = sourceValue index) ∧
      ∃ baseValue : GKRAddress → Source.BaseField, ∃ values : GKRAddress → R,
        (∀ wire, baseValue (Airbender.Compiler.FullArithmeticNative.MulDivCached.native.inputBank.address wire) = sourceExtended wire) ∧
        (∀ gate ∈ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.artifact.gates, gate.expressionResidual (baseValue ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) = 0) ∧
        (∀ address, Airbender.Compiler.FunctionalNative.MulDivCached.native.isBase address = true → values address = hom (baseValue address)) ∧
        (∀ definition ∈ Airbender.Compiler.FunctionalNative.MulDivCached.native.definitions, definition.Holds hom challenges values) ∧
        (∀ gate ∈ Airbender.Compiler.LookupNative.MulDivCached.native.gates, gate.Holds hom challenges gamma values) ∧
        (∀ gate ∈ Airbender.Compiler.ProductNative.MulDivCached.native.gates, gate.Holds hom challenges values) := by
  obtain ⟨sourceExtended, frame, holds⟩ := native.source_contract_extension sourceValue original clockValid
  refine ⟨sourceExtended, frame, ?_⟩
  exact Airbender.Compiler.FunctionalNative.MulDivCached.native.full_graph_extends hom challenges gamma sourceExtended holds fallback

end Airbender.Compiler.SourceContractNative.MulDivCached
