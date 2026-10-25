import GKRProtocol.FunctionalLinksImport
import GKRProtocol.FunctionalNative.BlakeRoundCached
import GKRProtocol.LookupSourceNative.BlakeRoundCached
import GKRProtocol.MemoryNative.BlakeRoundCached
import GKRProtocol.HelperNative.BlakeRoundCached

namespace Airbender.Compiler.FunctionalLinksNative.BlakeRoundCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_functional_links native from "artifacts/compiler/blake-round-cached.json"
  graph Airbender.Compiler.FunctionalNative.BlakeRoundCached.native
  base_model Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native
  typing Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing
  lookup_fields Airbender.Compiler.LookupNative.BlakeRoundCached.native
  lookup_source Airbender.Compiler.LookupSourceNative.BlakeRoundCached.native
  memory_model Airbender.Compiler.MemoryNative.BlakeRoundCached.native
  helper_model Airbender.Compiler.HelperNative.BlakeRoundCached.native

theorem timestamp_source_witness {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (baseValue : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.artifact.gates,
      gate.expressionResidual (baseValue ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0) :
    (Airbender.Compiler.LookupNative.BlakeRoundCached.native.timestampOutput).value ((native.assignment hom challenges gamma baseValue).value Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing hom) =
      (Airbender.Compiler.HelperNative.BlakeRoundCached.native.timestampTerms hom challenges gamma (native.assignment hom challenges gamma baseValue)).sum :=
  Airbender.Compiler.HelperNative.BlakeRoundCached.native.timestampSourceReduction hom challenges gamma
    (native.assignment hom challenges gamma baseValue)
    (native.helperDefined hom challenges gamma baseValue arithmetic)
    (native.helperCopies baseValue arithmetic)
    (by rw [native.assignment_value]; exact Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.canonical_lookups hom challenges gamma baseValue)

theorem generic_source_witness {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (baseValue : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.artifact.gates,
      gate.expressionResidual (baseValue ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0) :
    (Airbender.Compiler.LookupNative.BlakeRoundCached.native.genericOutput).value ((native.assignment hom challenges gamma baseValue).value Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing hom) =
      (Airbender.Compiler.LookupSourceNative.BlakeRoundCached.native.genericSourceTerms hom challenges gamma (native.assignment hom challenges gamma baseValue)).sum :=
  Airbender.Compiler.LookupSourceNative.BlakeRoundCached.native.genericSourceReduction hom challenges gamma
    (native.assignment hom challenges gamma baseValue)
    (native.lookupDefined hom challenges gamma baseValue arithmetic)
    (native.lookupCopies baseValue arithmetic)
    (by rw [native.assignment_value]; exact Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.canonical_lookups hom challenges gamma baseValue)

theorem memoryRead_source_witness {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (baseValue : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.artifact.gates,
      gate.expressionResidual (baseValue ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0) :
    ((native.assignment hom challenges gamma baseValue).value Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing hom) (GKRAddress.InnerLayer 8 2) =
      maskProduct (hom (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourceExecute.value (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourceValues baseValue)))
      (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadTerms hom challenges (native.assignment hom challenges gamma baseValue)).prod :=
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadSourceReduction hom challenges
    (native.assignment hom challenges gamma baseValue)
    (native.memoryDefined hom challenges gamma baseValue arithmetic)
    (native.memoryCopies baseValue arithmetic)
    (by rw [native.assignment_value]; exact Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.canonical_products hom challenges gamma baseValue)

theorem memoryWrite_source_witness {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (baseValue : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.artifact.gates,
      gate.expressionResidual (baseValue ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0) :
    ((native.assignment hom challenges gamma baseValue).value Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing hom) (GKRAddress.InnerLayer 8 3) =
      maskProduct (hom (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourceExecute.value (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourceValues baseValue)))
      (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteTerms hom challenges (native.assignment hom challenges gamma baseValue)).prod :=
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteSourceReduction hom challenges
    (native.assignment hom challenges gamma baseValue)
    (native.memoryDefined hom challenges gamma baseValue arithmetic)
    (native.memoryCopies baseValue arithmetic)
    (by rw [native.assignment_value]; exact Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.canonical_products hom challenges gamma baseValue)

end Airbender.Compiler.FunctionalLinksNative.BlakeRoundCached
