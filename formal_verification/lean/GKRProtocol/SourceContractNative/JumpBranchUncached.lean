import GKRProtocol.SourceContractImport
import GKRProtocol.FunctionalNative.JumpBranchUncached

namespace Airbender.Compiler.SourceContractNative.JumpBranchUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_compiler_source_contract native from "artifacts/compiler/jump-branch-uncached.json"
  source "artifacts/compiler/jump-branch-uncached-source.json" base_model Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native inputs 55

theorem source_contract_graph_extends {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (sourceValue : Fin Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.inputs.length → Source.BaseField)
    (original : Satisfies (native.originals.map Expression.polynomial) sourceValue)
    (clockValid : Source.clockContract native.clock (Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.helperPlacement.memory.project sourceValue))
    (fallback : GKRAddress → Source.BaseField) :
    ∃ sourceExtended : Fin Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.inputs.length → Source.BaseField,
      (∀ index, (∀ borrow, native.slots borrow ≠ index) → sourceExtended index = sourceValue index) ∧
      ∃ baseValue : GKRAddress → Source.BaseField, ∃ values : GKRAddress → R,
        (∀ wire, baseValue (Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.inputBank.address wire) = sourceExtended wire) ∧
        (∀ gate ∈ Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.artifact.gates, gate.expressionResidual (baseValue ∘ Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.bank.address) = 0) ∧
        (∀ address, Airbender.Compiler.FunctionalNative.JumpBranchUncached.native.isBase address = true → values address = hom (baseValue address)) ∧
        (∀ definition ∈ Airbender.Compiler.FunctionalNative.JumpBranchUncached.native.definitions, definition.Holds hom challenges values) ∧
        (∀ gate ∈ Airbender.Compiler.LookupNative.JumpBranchUncached.native.gates, gate.Holds hom challenges gamma values) ∧
        (∀ gate ∈ Airbender.Compiler.ProductNative.JumpBranchUncached.native.gates, gate.Holds hom challenges values) := by
  obtain ⟨sourceExtended, frame, holds⟩ := native.source_contract_extension sourceValue original clockValid
  refine ⟨sourceExtended, frame, ?_⟩
  exact Airbender.Compiler.FunctionalNative.JumpBranchUncached.native.full_graph_extends hom challenges gamma sourceExtended holds fallback

end Airbender.Compiler.SourceContractNative.JumpBranchUncached
