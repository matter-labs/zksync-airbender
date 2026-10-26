import Airbender.Import.GKRProtocol.FunctionalLinksImport
import Airbender.Proofs.GKRProtocol.FunctionalNative.WordMemoryUncached
import Airbender.Proofs.GKRProtocol.LookupSourceNative.WordMemoryUncached
import Airbender.Proofs.GKRProtocol.MemoryNative.WordMemoryUncached
import Airbender.Proofs.GKRProtocol.HelperNative.WordMemoryUncached

namespace Airbender.Compiler.FunctionalLinksNative.WordMemoryUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_functional_links native from "artifacts/compiler/word-memory-uncached.json"
  graph Airbender.Compiler.FunctionalNative.WordMemoryUncached.native
  base_model Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native
  typing Airbender.Compiler.ConsumerNative.WordMemoryUncached.native.typing
  lookup_fields Airbender.Compiler.LookupNative.WordMemoryUncached.native
  lookup_source Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native
  memory_model Airbender.Compiler.MemoryNative.WordMemoryUncached.native
  helper_model Airbender.Compiler.HelperNative.WordMemoryUncached.native

theorem timestamp_source_witness {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (baseValue : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.artifact.gates,
      gate.expressionResidual (baseValue ∘ Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.bank.address) = 0) :
    (Airbender.Compiler.LookupNative.WordMemoryUncached.native.timestampOutput).value ((native.assignment hom challenges gamma baseValue).value Airbender.Compiler.ConsumerNative.WordMemoryUncached.native.typing hom) =
      (Airbender.Compiler.HelperNative.WordMemoryUncached.native.timestampTerms hom challenges gamma (native.assignment hom challenges gamma baseValue)).sum :=
  Airbender.Compiler.HelperNative.WordMemoryUncached.native.timestampSourceReduction hom challenges gamma
    (native.assignment hom challenges gamma baseValue)
    (native.helperDefined hom challenges gamma baseValue arithmetic)
    (native.helperCopies baseValue arithmetic)
    (by rw [native.assignment_value]; exact Airbender.Compiler.FunctionalNative.WordMemoryUncached.native.canonical_lookups hom challenges gamma baseValue)

theorem generic_source_witness {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (baseValue : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.artifact.gates,
      gate.expressionResidual (baseValue ∘ Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.bank.address) = 0) :
    (Airbender.Compiler.LookupNative.WordMemoryUncached.native.genericOutput).value ((native.assignment hom challenges gamma baseValue).value Airbender.Compiler.ConsumerNative.WordMemoryUncached.native.typing hom) =
      (Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.genericSourceTerms hom challenges gamma (native.assignment hom challenges gamma baseValue)).sum :=
  Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.genericSourceReduction hom challenges gamma
    (native.assignment hom challenges gamma baseValue)
    (native.lookupDefined hom challenges gamma baseValue arithmetic)
    (native.lookupCopies baseValue arithmetic)
    (by rw [native.assignment_value]; exact Airbender.Compiler.FunctionalNative.WordMemoryUncached.native.canonical_lookups hom challenges gamma baseValue)

theorem range16_source_witness {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (baseValue : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.artifact.gates,
      gate.expressionResidual (baseValue ∘ Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.bank.address) = 0) :
    (Airbender.Compiler.LookupNative.WordMemoryUncached.native.range16Output).value ((native.assignment hom challenges gamma baseValue).value Airbender.Compiler.ConsumerNative.WordMemoryUncached.native.typing hom) =
      (Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.range16SourceTerms hom challenges gamma (native.assignment hom challenges gamma baseValue)).sum :=
  Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.range16SourceReduction hom challenges gamma
    (native.assignment hom challenges gamma baseValue)
    (native.lookupDefined hom challenges gamma baseValue arithmetic)
    (native.lookupCopies baseValue arithmetic)
    (by rw [native.assignment_value]; exact Airbender.Compiler.FunctionalNative.WordMemoryUncached.native.canonical_lookups hom challenges gamma baseValue)

theorem memoryRead_source_witness {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (baseValue : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.artifact.gates,
      gate.expressionResidual (baseValue ∘ Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.bank.address) = 0) :
    ((native.assignment hom challenges gamma baseValue).value Airbender.Compiler.ConsumerNative.WordMemoryUncached.native.typing hom) (GKRAddress.InnerLayer 4 2) =
      maskProduct (hom (Airbender.Compiler.MemoryNative.WordMemoryUncached.native.sourceExecute.value (Airbender.Compiler.MemoryNative.WordMemoryUncached.native.sourceValues baseValue)))
      (Airbender.Compiler.MemoryNative.WordMemoryUncached.native.memoryReadTerms hom challenges (native.assignment hom challenges gamma baseValue)).prod :=
  Airbender.Compiler.MemoryNative.WordMemoryUncached.native.memoryReadSourceReduction hom challenges
    (native.assignment hom challenges gamma baseValue)
    (native.memoryDefined hom challenges gamma baseValue arithmetic)
    (native.memoryCopies baseValue arithmetic)
    (by rw [native.assignment_value]; exact Airbender.Compiler.FunctionalNative.WordMemoryUncached.native.canonical_products hom challenges gamma baseValue)

theorem memoryWrite_source_witness {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (baseValue : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.artifact.gates,
      gate.expressionResidual (baseValue ∘ Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.bank.address) = 0) :
    ((native.assignment hom challenges gamma baseValue).value Airbender.Compiler.ConsumerNative.WordMemoryUncached.native.typing hom) (GKRAddress.InnerLayer 4 3) =
      maskProduct (hom (Airbender.Compiler.MemoryNative.WordMemoryUncached.native.sourceExecute.value (Airbender.Compiler.MemoryNative.WordMemoryUncached.native.sourceValues baseValue)))
      (Airbender.Compiler.MemoryNative.WordMemoryUncached.native.memoryWriteTerms hom challenges (native.assignment hom challenges gamma baseValue)).prod :=
  Airbender.Compiler.MemoryNative.WordMemoryUncached.native.memoryWriteSourceReduction hom challenges
    (native.assignment hom challenges gamma baseValue)
    (native.memoryDefined hom challenges gamma baseValue arithmetic)
    (native.memoryCopies baseValue arithmetic)
    (by rw [native.assignment_value]; exact Airbender.Compiler.FunctionalNative.WordMemoryUncached.native.canonical_products hom challenges gamma baseValue)

end Airbender.Compiler.FunctionalLinksNative.WordMemoryUncached
