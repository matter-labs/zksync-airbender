import GKRProtocol.FunctionalLinksImport
import GKRProtocol.FunctionalNative.BlakeRoundUncached
import GKRProtocol.LookupSourceNative.BlakeRoundUncached
import GKRProtocol.MemoryNative.BlakeRoundUncached
import GKRProtocol.HelperNative.BlakeRoundUncached

namespace Airbender.Compiler.FunctionalLinksNative.BlakeRoundUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_functional_links native from "artifacts/compiler/blake-round-uncached.json"
  graph Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native
  base_model Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native
  typing Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing
  lookup_fields Airbender.Compiler.LookupNative.BlakeRoundUncached.native
  lookup_source Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native
  memory_model Airbender.Compiler.MemoryNative.BlakeRoundUncached.native
  helper_model Airbender.Compiler.HelperNative.BlakeRoundUncached.native

theorem timestamp_source_witness {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (baseValue : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.artifact.gates,
      gate.expressionResidual (baseValue ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.bank.address) = 0) :
    (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.timestampOutput).value ((native.assignment hom challenges gamma baseValue).value Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing hom) =
      (Airbender.Compiler.HelperNative.BlakeRoundUncached.native.timestampTerms hom challenges gamma (native.assignment hom challenges gamma baseValue)).sum :=
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.timestampSourceReduction hom challenges gamma
    (native.assignment hom challenges gamma baseValue)
    (native.helperDefined hom challenges gamma baseValue arithmetic)
    (native.helperCopies baseValue arithmetic)
    (by rw [native.assignment_value]; exact Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.canonical_lookups hom challenges gamma baseValue)

theorem generic_source_witness {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (baseValue : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.artifact.gates,
      gate.expressionResidual (baseValue ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.bank.address) = 0) :
    (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.genericOutput).value ((native.assignment hom challenges gamma baseValue).value Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing hom) =
      (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.genericSourceTerms hom challenges gamma (native.assignment hom challenges gamma baseValue)).sum :=
  Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.genericSourceReduction hom challenges gamma
    (native.assignment hom challenges gamma baseValue)
    (native.lookupDefined hom challenges gamma baseValue arithmetic)
    (native.lookupCopies baseValue arithmetic)
    (by rw [native.assignment_value]; exact Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.canonical_lookups hom challenges gamma baseValue)

theorem memoryRead_source_witness {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (baseValue : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.artifact.gates,
      gate.expressionResidual (baseValue ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.bank.address) = 0) :
    ((native.assignment hom challenges gamma baseValue).value Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing hom) (GKRAddress.InnerLayer 8 2) =
      maskProduct (hom (Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.sourceExecute.value (Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.sourceValues baseValue)))
      (Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.memoryReadTerms hom challenges (native.assignment hom challenges gamma baseValue)).prod :=
  Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.memoryReadSourceReduction hom challenges
    (native.assignment hom challenges gamma baseValue)
    (native.memoryDefined hom challenges gamma baseValue arithmetic)
    (native.memoryCopies baseValue arithmetic)
    (by rw [native.assignment_value]; exact Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.canonical_products hom challenges gamma baseValue)

theorem memoryWrite_source_witness {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (baseValue : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.artifact.gates,
      gate.expressionResidual (baseValue ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.bank.address) = 0) :
    ((native.assignment hom challenges gamma baseValue).value Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing hom) (GKRAddress.InnerLayer 8 3) =
      maskProduct (hom (Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.sourceExecute.value (Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.sourceValues baseValue)))
      (Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.memoryWriteTerms hom challenges (native.assignment hom challenges gamma baseValue)).prod :=
  Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.memoryWriteSourceReduction hom challenges
    (native.assignment hom challenges gamma baseValue)
    (native.memoryDefined hom challenges gamma baseValue arithmetic)
    (native.memoryCopies baseValue arithmetic)
    (by rw [native.assignment_value]; exact Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.canonical_products hom challenges gamma baseValue)

end Airbender.Compiler.FunctionalLinksNative.BlakeRoundUncached
