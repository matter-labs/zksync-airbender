import Airbender.Import.GKRProtocol.SourceContractImport
import Airbender.Proofs.GKRProtocol.FunctionalNative.SubwordMemoryCached

namespace Airbender.Compiler.SourceContractNative.SubwordMemoryCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_compiler_source_contract native from "artifacts/compiler/subword-memory-cached.json"
  source "artifacts/compiler/subword-memory-cached-source.json" base_model Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native inputs 68

theorem source_contract_graph_extends {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (sourceValue : Fin Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.inputs.length → Source.BaseField)
    (original : Satisfies (native.originals.map Expression.polynomial) sourceValue)
    (clockValid : Source.clockContract native.clock (Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.helperPlacement.memory.project sourceValue))
    (fallback : GKRAddress → Source.BaseField) :
    ∃ sourceExtended : Fin Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.inputs.length → Source.BaseField,
      (∀ index, (∀ borrow, native.slots borrow ≠ index) → sourceExtended index = sourceValue index) ∧
      ∃ baseValue : GKRAddress → Source.BaseField, ∃ values : GKRAddress → R,
        (∀ wire, baseValue (Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.inputBank.address wire) = sourceExtended wire) ∧
        (∀ gate ∈ Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.artifact.gates, gate.expressionResidual (baseValue ∘ Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.bank.address) = 0) ∧
        (∀ address, Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.isBase address = true → values address = hom (baseValue address)) ∧
        (∀ definition ∈ Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.definitions, definition.Holds hom challenges values) ∧
        (∀ gate ∈ Airbender.Compiler.LookupNative.SubwordMemoryCached.native.gates, gate.Holds hom challenges gamma values) ∧
        (∀ gate ∈ Airbender.Compiler.ProductNative.SubwordMemoryCached.native.gates, gate.Holds hom challenges values) := by
  obtain ⟨sourceExtended, frame, holds⟩ := native.source_contract_extension sourceValue original clockValid
  refine ⟨sourceExtended, frame, ?_⟩
  exact Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.full_graph_extends hom challenges gamma sourceExtended holds fallback

end Airbender.Compiler.SourceContractNative.SubwordMemoryCached
