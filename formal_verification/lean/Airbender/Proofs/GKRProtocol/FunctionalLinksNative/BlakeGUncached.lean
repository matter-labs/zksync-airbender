import Airbender.Import.GKRProtocol.FunctionalLinksImport
import Airbender.Proofs.GKRProtocol.FunctionalNative.BlakeGUncached
import Airbender.Proofs.GKRProtocol.LookupSourceNative.BlakeGUncached
import Airbender.Proofs.GKRProtocol.MemoryNative.BlakeGUncached
import Airbender.Proofs.GKRProtocol.HelperNative.BlakeGUncached

namespace Airbender.Compiler.FunctionalLinksNative.BlakeGUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_functional_links native from "artifacts/compiler/blake-g-uncached.json"
  graph Airbender.Compiler.FunctionalNative.BlakeGUncached.native
  base_model Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native
  typing Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing
  lookup_fields Airbender.Compiler.LookupNative.BlakeGUncached.native
  lookup_source Airbender.Compiler.LookupSourceNative.BlakeGUncached.native
  memory_model Airbender.Compiler.MemoryNative.BlakeGUncached.native
  helper_model Airbender.Compiler.HelperNative.BlakeGUncached.native

theorem timestamp_source_witness {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (baseValue : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.artifact.gates,
      gate.expressionResidual (baseValue ∘ Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.bank.address) = 0) :
    (Airbender.Compiler.LookupNative.BlakeGUncached.native.timestampOutput).value ((native.assignment hom challenges gamma baseValue).value Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing hom) =
      (Airbender.Compiler.HelperNative.BlakeGUncached.native.timestampTerms hom challenges gamma (native.assignment hom challenges gamma baseValue)).sum :=
  Airbender.Compiler.HelperNative.BlakeGUncached.native.timestampSourceReduction hom challenges gamma
    (native.assignment hom challenges gamma baseValue)
    (native.helperDefined hom challenges gamma baseValue arithmetic)
    (native.helperCopies baseValue arithmetic)
    (by rw [native.assignment_value]; exact Airbender.Compiler.FunctionalNative.BlakeGUncached.native.canonical_lookups hom challenges gamma baseValue)

theorem generic_source_witness {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (baseValue : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.artifact.gates,
      gate.expressionResidual (baseValue ∘ Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.bank.address) = 0) :
    (Airbender.Compiler.LookupNative.BlakeGUncached.native.genericOutput).value ((native.assignment hom challenges gamma baseValue).value Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing hom) =
      (Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.genericSourceTerms hom challenges gamma (native.assignment hom challenges gamma baseValue)).sum :=
  Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.genericSourceReduction hom challenges gamma
    (native.assignment hom challenges gamma baseValue)
    (native.lookupDefined hom challenges gamma baseValue arithmetic)
    (native.lookupCopies baseValue arithmetic)
    (by rw [native.assignment_value]; exact Airbender.Compiler.FunctionalNative.BlakeGUncached.native.canonical_lookups hom challenges gamma baseValue)

theorem memoryRead_source_witness {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (baseValue : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.artifact.gates,
      gate.expressionResidual (baseValue ∘ Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.bank.address) = 0) :
    ((native.assignment hom challenges gamma baseValue).value Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing hom) (GKRAddress.InnerLayer 5 0) =
      maskProduct (hom (Airbender.Compiler.MemoryNative.BlakeGUncached.native.sourceExecute.value (Airbender.Compiler.MemoryNative.BlakeGUncached.native.sourceValues baseValue)))
      (Airbender.Compiler.MemoryNative.BlakeGUncached.native.memoryReadTerms hom challenges (native.assignment hom challenges gamma baseValue)).prod :=
  Airbender.Compiler.MemoryNative.BlakeGUncached.native.memoryReadSourceReduction hom challenges
    (native.assignment hom challenges gamma baseValue)
    (native.memoryDefined hom challenges gamma baseValue arithmetic)
    (native.memoryCopies baseValue arithmetic)
    (by rw [native.assignment_value]; exact Airbender.Compiler.FunctionalNative.BlakeGUncached.native.canonical_products hom challenges gamma baseValue)

theorem memoryWrite_source_witness {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (baseValue : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.artifact.gates,
      gate.expressionResidual (baseValue ∘ Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.bank.address) = 0) :
    ((native.assignment hom challenges gamma baseValue).value Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing hom) (GKRAddress.InnerLayer 5 1) =
      maskProduct (hom (Airbender.Compiler.MemoryNative.BlakeGUncached.native.sourceExecute.value (Airbender.Compiler.MemoryNative.BlakeGUncached.native.sourceValues baseValue)))
      (Airbender.Compiler.MemoryNative.BlakeGUncached.native.memoryWriteTerms hom challenges (native.assignment hom challenges gamma baseValue)).prod :=
  Airbender.Compiler.MemoryNative.BlakeGUncached.native.memoryWriteSourceReduction hom challenges
    (native.assignment hom challenges gamma baseValue)
    (native.memoryDefined hom challenges gamma baseValue arithmetic)
    (native.memoryCopies baseValue arithmetic)
    (by rw [native.assignment_value]; exact Airbender.Compiler.FunctionalNative.BlakeGUncached.native.canonical_products hom challenges gamma baseValue)

end Airbender.Compiler.FunctionalLinksNative.BlakeGUncached
