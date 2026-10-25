import GKRProtocol.FunctionalLinksImport
import GKRProtocol.FunctionalNative.AddSubCached
import GKRProtocol.LookupSourceNative.AddSubCached
import GKRProtocol.MemoryNative.AddSubCached
import GKRProtocol.HelperNative.AddSubCached

namespace Airbender.Compiler.FunctionalLinksNative.AddSubCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_functional_links native from "artifacts/compiler/add-sub-cached.json"
  graph Airbender.Compiler.FunctionalNative.AddSubCached.native
  base_model Airbender.Compiler.FullArithmeticNative.AddSubCached.native
  typing Airbender.Compiler.ConsumerNative.AddSubCached.native.typing
  lookup_fields Airbender.Compiler.LookupNative.AddSubCached.native
  lookup_source Airbender.Compiler.LookupSourceNative.AddSubCached.native
  memory_model Airbender.Compiler.MemoryNative.AddSubCached.native
  helper_model Airbender.Compiler.HelperNative.AddSubCached.native

theorem timestamp_source_witness {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (baseValue : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.artifact.gates,
      gate.expressionResidual (baseValue ∘ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address) = 0) :
    (Airbender.Compiler.LookupNative.AddSubCached.native.timestampOutput).value ((native.assignment hom challenges gamma baseValue).value Airbender.Compiler.ConsumerNative.AddSubCached.native.typing hom) =
      (Airbender.Compiler.HelperNative.AddSubCached.native.timestampTerms hom challenges gamma (native.assignment hom challenges gamma baseValue)).sum :=
  Airbender.Compiler.HelperNative.AddSubCached.native.timestampSourceReduction hom challenges gamma
    (native.assignment hom challenges gamma baseValue)
    (native.helperDefined hom challenges gamma baseValue arithmetic)
    (native.helperCopies baseValue arithmetic)
    (by rw [native.assignment_value]; exact Airbender.Compiler.FunctionalNative.AddSubCached.native.canonical_lookups hom challenges gamma baseValue)

theorem generic_source_witness {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (baseValue : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.artifact.gates,
      gate.expressionResidual (baseValue ∘ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address) = 0) :
    (Airbender.Compiler.LookupNative.AddSubCached.native.genericOutput).value ((native.assignment hom challenges gamma baseValue).value Airbender.Compiler.ConsumerNative.AddSubCached.native.typing hom) =
      (Airbender.Compiler.LookupSourceNative.AddSubCached.native.genericSourceTerms hom challenges gamma (native.assignment hom challenges gamma baseValue)).sum :=
  Airbender.Compiler.LookupSourceNative.AddSubCached.native.genericSourceReduction hom challenges gamma
    (native.assignment hom challenges gamma baseValue)
    (native.lookupDefined hom challenges gamma baseValue arithmetic)
    (native.lookupCopies baseValue arithmetic)
    (by rw [native.assignment_value]; exact Airbender.Compiler.FunctionalNative.AddSubCached.native.canonical_lookups hom challenges gamma baseValue)

theorem range16_source_witness {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (baseValue : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.artifact.gates,
      gate.expressionResidual (baseValue ∘ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address) = 0) :
    (Airbender.Compiler.LookupNative.AddSubCached.native.range16Output).value ((native.assignment hom challenges gamma baseValue).value Airbender.Compiler.ConsumerNative.AddSubCached.native.typing hom) =
      (Airbender.Compiler.LookupSourceNative.AddSubCached.native.range16SourceTerms hom challenges gamma (native.assignment hom challenges gamma baseValue)).sum :=
  Airbender.Compiler.LookupSourceNative.AddSubCached.native.range16SourceReduction hom challenges gamma
    (native.assignment hom challenges gamma baseValue)
    (native.lookupDefined hom challenges gamma baseValue arithmetic)
    (native.lookupCopies baseValue arithmetic)
    (by rw [native.assignment_value]; exact Airbender.Compiler.FunctionalNative.AddSubCached.native.canonical_lookups hom challenges gamma baseValue)

theorem memoryRead_source_witness {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (baseValue : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.artifact.gates,
      gate.expressionResidual (baseValue ∘ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address) = 0) :
    ((native.assignment hom challenges gamma baseValue).value Airbender.Compiler.ConsumerNative.AddSubCached.native.typing hom) (GKRAddress.InnerLayer 4 2) =
      maskProduct (hom (Airbender.Compiler.MemoryNative.AddSubCached.native.sourceExecute.value (Airbender.Compiler.MemoryNative.AddSubCached.native.sourceValues baseValue)))
      (Airbender.Compiler.MemoryNative.AddSubCached.native.memoryReadTerms hom challenges (native.assignment hom challenges gamma baseValue)).prod :=
  Airbender.Compiler.MemoryNative.AddSubCached.native.memoryReadSourceReduction hom challenges
    (native.assignment hom challenges gamma baseValue)
    (native.memoryDefined hom challenges gamma baseValue arithmetic)
    (native.memoryCopies baseValue arithmetic)
    (by rw [native.assignment_value]; exact Airbender.Compiler.FunctionalNative.AddSubCached.native.canonical_products hom challenges gamma baseValue)

theorem memoryWrite_source_witness {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (baseValue : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.artifact.gates,
      gate.expressionResidual (baseValue ∘ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address) = 0) :
    ((native.assignment hom challenges gamma baseValue).value Airbender.Compiler.ConsumerNative.AddSubCached.native.typing hom) (GKRAddress.InnerLayer 4 3) =
      maskProduct (hom (Airbender.Compiler.MemoryNative.AddSubCached.native.sourceExecute.value (Airbender.Compiler.MemoryNative.AddSubCached.native.sourceValues baseValue)))
      (Airbender.Compiler.MemoryNative.AddSubCached.native.memoryWriteTerms hom challenges (native.assignment hom challenges gamma baseValue)).prod :=
  Airbender.Compiler.MemoryNative.AddSubCached.native.memoryWriteSourceReduction hom challenges
    (native.assignment hom challenges gamma baseValue)
    (native.memoryDefined hom challenges gamma baseValue arithmetic)
    (native.memoryCopies baseValue arithmetic)
    (by rw [native.assignment_value]; exact Airbender.Compiler.FunctionalNative.AddSubCached.native.canonical_products hom challenges gamma baseValue)

end Airbender.Compiler.FunctionalLinksNative.AddSubCached
