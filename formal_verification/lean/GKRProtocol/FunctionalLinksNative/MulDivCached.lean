import GKRProtocol.FunctionalLinksImport
import GKRProtocol.FunctionalNative.MulDivCached
import GKRProtocol.LookupSourceNative.MulDivCached
import GKRProtocol.MemoryNative.MulDivCached
import GKRProtocol.HelperNative.MulDivCached

namespace Airbender.Compiler.FunctionalLinksNative.MulDivCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_functional_links native from "artifacts/compiler/mul-div-cached.json"
  graph Airbender.Compiler.FunctionalNative.MulDivCached.native
  base_model Airbender.Compiler.FullArithmeticNative.MulDivCached.native
  typing Airbender.Compiler.ConsumerNative.MulDivCached.native.typing
  lookup_fields Airbender.Compiler.LookupNative.MulDivCached.native
  lookup_source Airbender.Compiler.LookupSourceNative.MulDivCached.native
  memory_model Airbender.Compiler.MemoryNative.MulDivCached.native
  helper_model Airbender.Compiler.HelperNative.MulDivCached.native

theorem timestamp_source_witness {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (baseValue : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.artifact.gates,
      gate.expressionResidual (baseValue ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) = 0) :
    (Airbender.Compiler.LookupNative.MulDivCached.native.timestampOutput).value ((native.assignment hom challenges gamma baseValue).value Airbender.Compiler.ConsumerNative.MulDivCached.native.typing hom) =
      (Airbender.Compiler.HelperNative.MulDivCached.native.timestampTerms hom challenges gamma (native.assignment hom challenges gamma baseValue)).sum :=
  Airbender.Compiler.HelperNative.MulDivCached.native.timestampSourceReduction hom challenges gamma
    (native.assignment hom challenges gamma baseValue)
    (native.helperDefined hom challenges gamma baseValue arithmetic)
    (native.helperCopies baseValue arithmetic)
    (by rw [native.assignment_value]; exact Airbender.Compiler.FunctionalNative.MulDivCached.native.canonical_lookups hom challenges gamma baseValue)

theorem generic_source_witness {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (baseValue : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.artifact.gates,
      gate.expressionResidual (baseValue ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) = 0) :
    (Airbender.Compiler.LookupNative.MulDivCached.native.genericOutput).value ((native.assignment hom challenges gamma baseValue).value Airbender.Compiler.ConsumerNative.MulDivCached.native.typing hom) =
      (Airbender.Compiler.LookupSourceNative.MulDivCached.native.genericSourceTerms hom challenges gamma (native.assignment hom challenges gamma baseValue)).sum :=
  Airbender.Compiler.LookupSourceNative.MulDivCached.native.genericSourceReduction hom challenges gamma
    (native.assignment hom challenges gamma baseValue)
    (native.lookupDefined hom challenges gamma baseValue arithmetic)
    (native.lookupCopies baseValue arithmetic)
    (by rw [native.assignment_value]; exact Airbender.Compiler.FunctionalNative.MulDivCached.native.canonical_lookups hom challenges gamma baseValue)

theorem range16_source_witness {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (baseValue : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.artifact.gates,
      gate.expressionResidual (baseValue ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) = 0) :
    (Airbender.Compiler.LookupNative.MulDivCached.native.range16Output).value ((native.assignment hom challenges gamma baseValue).value Airbender.Compiler.ConsumerNative.MulDivCached.native.typing hom) =
      (Airbender.Compiler.LookupSourceNative.MulDivCached.native.range16SourceTerms hom challenges gamma (native.assignment hom challenges gamma baseValue)).sum :=
  Airbender.Compiler.LookupSourceNative.MulDivCached.native.range16SourceReduction hom challenges gamma
    (native.assignment hom challenges gamma baseValue)
    (native.lookupDefined hom challenges gamma baseValue arithmetic)
    (native.lookupCopies baseValue arithmetic)
    (by rw [native.assignment_value]; exact Airbender.Compiler.FunctionalNative.MulDivCached.native.canonical_lookups hom challenges gamma baseValue)

theorem memoryRead_source_witness {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (baseValue : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.artifact.gates,
      gate.expressionResidual (baseValue ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) = 0) :
    ((native.assignment hom challenges gamma baseValue).value Airbender.Compiler.ConsumerNative.MulDivCached.native.typing hom) (GKRAddress.InnerLayer 4 6) =
      maskProduct (hom (Airbender.Compiler.MemoryNative.MulDivCached.native.sourceExecute.value (Airbender.Compiler.MemoryNative.MulDivCached.native.sourceValues baseValue)))
      (Airbender.Compiler.MemoryNative.MulDivCached.native.memoryReadTerms hom challenges (native.assignment hom challenges gamma baseValue)).prod :=
  Airbender.Compiler.MemoryNative.MulDivCached.native.memoryReadSourceReduction hom challenges
    (native.assignment hom challenges gamma baseValue)
    (native.memoryDefined hom challenges gamma baseValue arithmetic)
    (native.memoryCopies baseValue arithmetic)
    (by rw [native.assignment_value]; exact Airbender.Compiler.FunctionalNative.MulDivCached.native.canonical_products hom challenges gamma baseValue)

theorem memoryWrite_source_witness {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (baseValue : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.artifact.gates,
      gate.expressionResidual (baseValue ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) = 0) :
    ((native.assignment hom challenges gamma baseValue).value Airbender.Compiler.ConsumerNative.MulDivCached.native.typing hom) (GKRAddress.InnerLayer 4 7) =
      maskProduct (hom (Airbender.Compiler.MemoryNative.MulDivCached.native.sourceExecute.value (Airbender.Compiler.MemoryNative.MulDivCached.native.sourceValues baseValue)))
      (Airbender.Compiler.MemoryNative.MulDivCached.native.memoryWriteTerms hom challenges (native.assignment hom challenges gamma baseValue)).prod :=
  Airbender.Compiler.MemoryNative.MulDivCached.native.memoryWriteSourceReduction hom challenges
    (native.assignment hom challenges gamma baseValue)
    (native.memoryDefined hom challenges gamma baseValue arithmetic)
    (native.memoryCopies baseValue arithmetic)
    (by rw [native.assignment_value]; exact Airbender.Compiler.FunctionalNative.MulDivCached.native.canonical_products hom challenges gamma baseValue)

end Airbender.Compiler.FunctionalLinksNative.MulDivCached
