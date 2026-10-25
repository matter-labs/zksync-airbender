import GKRProtocol.FunctionalLinksImport
import GKRProtocol.FunctionalNative.BigintCached
import GKRProtocol.LookupSourceNative.BigintCached
import GKRProtocol.MemoryNative.BigintCached
import GKRProtocol.HelperNative.BigintCached

namespace Airbender.Compiler.FunctionalLinksNative.BigintCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_functional_links native from "artifacts/compiler/bigint-cached.json"
  graph Airbender.Compiler.FunctionalNative.BigintCached.native
  base_model Airbender.Compiler.FullArithmeticNative.BigintCached.native
  typing Airbender.Compiler.ConsumerNative.BigintCached.native.typing
  lookup_fields Airbender.Compiler.LookupNative.BigintCached.native
  lookup_source Airbender.Compiler.LookupSourceNative.BigintCached.native
  memory_model Airbender.Compiler.MemoryNative.BigintCached.native
  helper_model Airbender.Compiler.HelperNative.BigintCached.native

theorem timestamp_source_witness {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (baseValue : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintCached.native.artifact.gates,
      gate.expressionResidual (baseValue ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) = 0) :
    (Airbender.Compiler.LookupNative.BigintCached.native.timestampOutput).value ((native.assignment hom challenges gamma baseValue).value Airbender.Compiler.ConsumerNative.BigintCached.native.typing hom) =
      (Airbender.Compiler.HelperNative.BigintCached.native.timestampTerms hom challenges gamma (native.assignment hom challenges gamma baseValue)).sum :=
  Airbender.Compiler.HelperNative.BigintCached.native.timestampSourceReduction hom challenges gamma
    (native.assignment hom challenges gamma baseValue)
    (native.helperDefined hom challenges gamma baseValue arithmetic)
    (native.helperCopies baseValue arithmetic)
    (by rw [native.assignment_value]; exact Airbender.Compiler.FunctionalNative.BigintCached.native.canonical_lookups hom challenges gamma baseValue)

theorem generic_source_witness {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (baseValue : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintCached.native.artifact.gates,
      gate.expressionResidual (baseValue ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) = 0) :
    (Airbender.Compiler.LookupNative.BigintCached.native.genericOutput).value ((native.assignment hom challenges gamma baseValue).value Airbender.Compiler.ConsumerNative.BigintCached.native.typing hom) =
      (Airbender.Compiler.LookupSourceNative.BigintCached.native.genericSourceTerms hom challenges gamma (native.assignment hom challenges gamma baseValue)).sum :=
  Airbender.Compiler.LookupSourceNative.BigintCached.native.genericSourceReduction hom challenges gamma
    (native.assignment hom challenges gamma baseValue)
    (native.lookupDefined hom challenges gamma baseValue arithmetic)
    (native.lookupCopies baseValue arithmetic)
    (by rw [native.assignment_value]; exact Airbender.Compiler.FunctionalNative.BigintCached.native.canonical_lookups hom challenges gamma baseValue)

theorem range16_source_witness {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (baseValue : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintCached.native.artifact.gates,
      gate.expressionResidual (baseValue ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) = 0) :
    (Airbender.Compiler.LookupNative.BigintCached.native.range16Output).value ((native.assignment hom challenges gamma baseValue).value Airbender.Compiler.ConsumerNative.BigintCached.native.typing hom) =
      (Airbender.Compiler.LookupSourceNative.BigintCached.native.range16SourceTerms hom challenges gamma (native.assignment hom challenges gamma baseValue)).sum :=
  Airbender.Compiler.LookupSourceNative.BigintCached.native.range16SourceReduction hom challenges gamma
    (native.assignment hom challenges gamma baseValue)
    (native.lookupDefined hom challenges gamma baseValue arithmetic)
    (native.lookupCopies baseValue arithmetic)
    (by rw [native.assignment_value]; exact Airbender.Compiler.FunctionalNative.BigintCached.native.canonical_lookups hom challenges gamma baseValue)

theorem memoryRead_source_witness {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (baseValue : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintCached.native.artifact.gates,
      gate.expressionResidual (baseValue ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) = 0) :
    ((native.assignment hom challenges gamma baseValue).value Airbender.Compiler.ConsumerNative.BigintCached.native.typing hom) (GKRAddress.InnerLayer 6 0) =
      maskProduct (hom (Airbender.Compiler.MemoryNative.BigintCached.native.sourceExecute.value (Airbender.Compiler.MemoryNative.BigintCached.native.sourceValues baseValue)))
      (Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadTerms hom challenges (native.assignment hom challenges gamma baseValue)).prod :=
  Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadSourceReduction hom challenges
    (native.assignment hom challenges gamma baseValue)
    (native.memoryDefined hom challenges gamma baseValue arithmetic)
    (native.memoryCopies baseValue arithmetic)
    (by rw [native.assignment_value]; exact Airbender.Compiler.FunctionalNative.BigintCached.native.canonical_products hom challenges gamma baseValue)

theorem memoryWrite_source_witness {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (baseValue : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintCached.native.artifact.gates,
      gate.expressionResidual (baseValue ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) = 0) :
    ((native.assignment hom challenges gamma baseValue).value Airbender.Compiler.ConsumerNative.BigintCached.native.typing hom) (GKRAddress.InnerLayer 6 1) =
      maskProduct (hom (Airbender.Compiler.MemoryNative.BigintCached.native.sourceExecute.value (Airbender.Compiler.MemoryNative.BigintCached.native.sourceValues baseValue)))
      (Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteTerms hom challenges (native.assignment hom challenges gamma baseValue)).prod :=
  Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteSourceReduction hom challenges
    (native.assignment hom challenges gamma baseValue)
    (native.memoryDefined hom challenges gamma baseValue arithmetic)
    (native.memoryCopies baseValue arithmetic)
    (by rw [native.assignment_value]; exact Airbender.Compiler.FunctionalNative.BigintCached.native.canonical_products hom challenges gamma baseValue)

end Airbender.Compiler.FunctionalLinksNative.BigintCached
