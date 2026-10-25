import GKRProtocol.FunctionalLinksImport
import GKRProtocol.FunctionalNative.JumpBranchUncached
import GKRProtocol.LookupSourceNative.JumpBranchUncached
import GKRProtocol.MemoryNative.JumpBranchUncached
import GKRProtocol.HelperNative.JumpBranchUncached

namespace Airbender.Compiler.FunctionalLinksNative.JumpBranchUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_functional_links native from "artifacts/compiler/jump-branch-uncached.json"
  graph Airbender.Compiler.FunctionalNative.JumpBranchUncached.native
  base_model Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native
  typing Airbender.Compiler.ConsumerNative.JumpBranchUncached.native.typing
  lookup_fields Airbender.Compiler.LookupNative.JumpBranchUncached.native
  lookup_source Airbender.Compiler.LookupSourceNative.JumpBranchUncached.native
  memory_model Airbender.Compiler.MemoryNative.JumpBranchUncached.native
  helper_model Airbender.Compiler.HelperNative.JumpBranchUncached.native

theorem timestamp_source_witness {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (baseValue : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.artifact.gates,
      gate.expressionResidual (baseValue ∘ Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.bank.address) = 0) :
    (Airbender.Compiler.LookupNative.JumpBranchUncached.native.timestampOutput).value ((native.assignment hom challenges gamma baseValue).value Airbender.Compiler.ConsumerNative.JumpBranchUncached.native.typing hom) =
      (Airbender.Compiler.HelperNative.JumpBranchUncached.native.timestampTerms hom challenges gamma (native.assignment hom challenges gamma baseValue)).sum :=
  Airbender.Compiler.HelperNative.JumpBranchUncached.native.timestampSourceReduction hom challenges gamma
    (native.assignment hom challenges gamma baseValue)
    (native.helperDefined hom challenges gamma baseValue arithmetic)
    (native.helperCopies baseValue arithmetic)
    (by rw [native.assignment_value]; exact Airbender.Compiler.FunctionalNative.JumpBranchUncached.native.canonical_lookups hom challenges gamma baseValue)

theorem generic_source_witness {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (baseValue : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.artifact.gates,
      gate.expressionResidual (baseValue ∘ Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.bank.address) = 0) :
    (Airbender.Compiler.LookupNative.JumpBranchUncached.native.genericOutput).value ((native.assignment hom challenges gamma baseValue).value Airbender.Compiler.ConsumerNative.JumpBranchUncached.native.typing hom) =
      (Airbender.Compiler.LookupSourceNative.JumpBranchUncached.native.genericSourceTerms hom challenges gamma (native.assignment hom challenges gamma baseValue)).sum :=
  Airbender.Compiler.LookupSourceNative.JumpBranchUncached.native.genericSourceReduction hom challenges gamma
    (native.assignment hom challenges gamma baseValue)
    (native.lookupDefined hom challenges gamma baseValue arithmetic)
    (native.lookupCopies baseValue arithmetic)
    (by rw [native.assignment_value]; exact Airbender.Compiler.FunctionalNative.JumpBranchUncached.native.canonical_lookups hom challenges gamma baseValue)

theorem range16_source_witness {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (baseValue : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.artifact.gates,
      gate.expressionResidual (baseValue ∘ Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.bank.address) = 0) :
    (Airbender.Compiler.LookupNative.JumpBranchUncached.native.range16Output).value ((native.assignment hom challenges gamma baseValue).value Airbender.Compiler.ConsumerNative.JumpBranchUncached.native.typing hom) =
      (Airbender.Compiler.LookupSourceNative.JumpBranchUncached.native.range16SourceTerms hom challenges gamma (native.assignment hom challenges gamma baseValue)).sum :=
  Airbender.Compiler.LookupSourceNative.JumpBranchUncached.native.range16SourceReduction hom challenges gamma
    (native.assignment hom challenges gamma baseValue)
    (native.lookupDefined hom challenges gamma baseValue arithmetic)
    (native.lookupCopies baseValue arithmetic)
    (by rw [native.assignment_value]; exact Airbender.Compiler.FunctionalNative.JumpBranchUncached.native.canonical_lookups hom challenges gamma baseValue)

theorem memoryRead_source_witness {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (baseValue : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.artifact.gates,
      gate.expressionResidual (baseValue ∘ Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.bank.address) = 0) :
    ((native.assignment hom challenges gamma baseValue).value Airbender.Compiler.ConsumerNative.JumpBranchUncached.native.typing hom) (GKRAddress.InnerLayer 4 2) =
      maskProduct (hom (Airbender.Compiler.MemoryNative.JumpBranchUncached.native.sourceExecute.value (Airbender.Compiler.MemoryNative.JumpBranchUncached.native.sourceValues baseValue)))
      (Airbender.Compiler.MemoryNative.JumpBranchUncached.native.memoryReadTerms hom challenges (native.assignment hom challenges gamma baseValue)).prod :=
  Airbender.Compiler.MemoryNative.JumpBranchUncached.native.memoryReadSourceReduction hom challenges
    (native.assignment hom challenges gamma baseValue)
    (native.memoryDefined hom challenges gamma baseValue arithmetic)
    (native.memoryCopies baseValue arithmetic)
    (by rw [native.assignment_value]; exact Airbender.Compiler.FunctionalNative.JumpBranchUncached.native.canonical_products hom challenges gamma baseValue)

theorem memoryWrite_source_witness {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (baseValue : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.artifact.gates,
      gate.expressionResidual (baseValue ∘ Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.bank.address) = 0) :
    ((native.assignment hom challenges gamma baseValue).value Airbender.Compiler.ConsumerNative.JumpBranchUncached.native.typing hom) (GKRAddress.InnerLayer 4 3) =
      maskProduct (hom (Airbender.Compiler.MemoryNative.JumpBranchUncached.native.sourceExecute.value (Airbender.Compiler.MemoryNative.JumpBranchUncached.native.sourceValues baseValue)))
      (Airbender.Compiler.MemoryNative.JumpBranchUncached.native.memoryWriteTerms hom challenges (native.assignment hom challenges gamma baseValue)).prod :=
  Airbender.Compiler.MemoryNative.JumpBranchUncached.native.memoryWriteSourceReduction hom challenges
    (native.assignment hom challenges gamma baseValue)
    (native.memoryDefined hom challenges gamma baseValue arithmetic)
    (native.memoryCopies baseValue arithmetic)
    (by rw [native.assignment_value]; exact Airbender.Compiler.FunctionalNative.JumpBranchUncached.native.canonical_products hom challenges gamma baseValue)

end Airbender.Compiler.FunctionalLinksNative.JumpBranchUncached
