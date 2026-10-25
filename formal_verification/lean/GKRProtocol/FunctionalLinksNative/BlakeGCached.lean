import GKRProtocol.FunctionalLinksImport
import GKRProtocol.FunctionalNative.BlakeGCached
import GKRProtocol.LookupSourceNative.BlakeGCached
import GKRProtocol.MemoryNative.BlakeGCached
import GKRProtocol.HelperNative.BlakeGCached

namespace Airbender.Compiler.FunctionalLinksNative.BlakeGCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_functional_links native from "artifacts/compiler/blake-g-cached.json"
  graph Airbender.Compiler.FunctionalNative.BlakeGCached.native
  base_model Airbender.Compiler.FullArithmeticNative.BlakeGCached.native
  typing Airbender.Compiler.ConsumerNative.BlakeGCached.native.typing
  lookup_fields Airbender.Compiler.LookupNative.BlakeGCached.native
  lookup_source Airbender.Compiler.LookupSourceNative.BlakeGCached.native
  memory_model Airbender.Compiler.MemoryNative.BlakeGCached.native
  helper_model Airbender.Compiler.HelperNative.BlakeGCached.native

theorem timestamp_source_witness {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (baseValue : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.artifact.gates,
      gate.expressionResidual (baseValue ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address) = 0) :
    (Airbender.Compiler.LookupNative.BlakeGCached.native.timestampOutput).value ((native.assignment hom challenges gamma baseValue).value Airbender.Compiler.ConsumerNative.BlakeGCached.native.typing hom) =
      (Airbender.Compiler.HelperNative.BlakeGCached.native.timestampTerms hom challenges gamma (native.assignment hom challenges gamma baseValue)).sum :=
  Airbender.Compiler.HelperNative.BlakeGCached.native.timestampSourceReduction hom challenges gamma
    (native.assignment hom challenges gamma baseValue)
    (native.helperDefined hom challenges gamma baseValue arithmetic)
    (native.helperCopies baseValue arithmetic)
    (by rw [native.assignment_value]; exact Airbender.Compiler.FunctionalNative.BlakeGCached.native.canonical_lookups hom challenges gamma baseValue)

theorem generic_source_witness {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (baseValue : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.artifact.gates,
      gate.expressionResidual (baseValue ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address) = 0) :
    (Airbender.Compiler.LookupNative.BlakeGCached.native.genericOutput).value ((native.assignment hom challenges gamma baseValue).value Airbender.Compiler.ConsumerNative.BlakeGCached.native.typing hom) =
      (Airbender.Compiler.LookupSourceNative.BlakeGCached.native.genericSourceTerms hom challenges gamma (native.assignment hom challenges gamma baseValue)).sum :=
  Airbender.Compiler.LookupSourceNative.BlakeGCached.native.genericSourceReduction hom challenges gamma
    (native.assignment hom challenges gamma baseValue)
    (native.lookupDefined hom challenges gamma baseValue arithmetic)
    (native.lookupCopies baseValue arithmetic)
    (by rw [native.assignment_value]; exact Airbender.Compiler.FunctionalNative.BlakeGCached.native.canonical_lookups hom challenges gamma baseValue)

theorem memoryRead_source_witness {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (baseValue : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.artifact.gates,
      gate.expressionResidual (baseValue ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address) = 0) :
    ((native.assignment hom challenges gamma baseValue).value Airbender.Compiler.ConsumerNative.BlakeGCached.native.typing hom) (GKRAddress.InnerLayer 5 0) =
      maskProduct (hom (Airbender.Compiler.MemoryNative.BlakeGCached.native.sourceExecute.value (Airbender.Compiler.MemoryNative.BlakeGCached.native.sourceValues baseValue)))
      (Airbender.Compiler.MemoryNative.BlakeGCached.native.memoryReadTerms hom challenges (native.assignment hom challenges gamma baseValue)).prod :=
  Airbender.Compiler.MemoryNative.BlakeGCached.native.memoryReadSourceReduction hom challenges
    (native.assignment hom challenges gamma baseValue)
    (native.memoryDefined hom challenges gamma baseValue arithmetic)
    (native.memoryCopies baseValue arithmetic)
    (by rw [native.assignment_value]; exact Airbender.Compiler.FunctionalNative.BlakeGCached.native.canonical_products hom challenges gamma baseValue)

theorem memoryWrite_source_witness {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (baseValue : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.artifact.gates,
      gate.expressionResidual (baseValue ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address) = 0) :
    ((native.assignment hom challenges gamma baseValue).value Airbender.Compiler.ConsumerNative.BlakeGCached.native.typing hom) (GKRAddress.InnerLayer 5 1) =
      maskProduct (hom (Airbender.Compiler.MemoryNative.BlakeGCached.native.sourceExecute.value (Airbender.Compiler.MemoryNative.BlakeGCached.native.sourceValues baseValue)))
      (Airbender.Compiler.MemoryNative.BlakeGCached.native.memoryWriteTerms hom challenges (native.assignment hom challenges gamma baseValue)).prod :=
  Airbender.Compiler.MemoryNative.BlakeGCached.native.memoryWriteSourceReduction hom challenges
    (native.assignment hom challenges gamma baseValue)
    (native.memoryDefined hom challenges gamma baseValue arithmetic)
    (native.memoryCopies baseValue arithmetic)
    (by rw [native.assignment_value]; exact Airbender.Compiler.FunctionalNative.BlakeGCached.native.canonical_products hom challenges gamma baseValue)

end Airbender.Compiler.FunctionalLinksNative.BlakeGCached
