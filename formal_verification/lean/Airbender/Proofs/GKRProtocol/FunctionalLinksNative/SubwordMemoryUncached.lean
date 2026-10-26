import Airbender.Import.GKRProtocol.FunctionalLinksImport
import Airbender.Proofs.GKRProtocol.FunctionalNative.SubwordMemoryUncached
import Airbender.Proofs.GKRProtocol.LookupSourceNative.SubwordMemoryUncached
import Airbender.Proofs.GKRProtocol.MemoryNative.SubwordMemoryUncached
import Airbender.Proofs.GKRProtocol.HelperNative.SubwordMemoryUncached

namespace Airbender.Compiler.FunctionalLinksNative.SubwordMemoryUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_functional_links native from "artifacts/compiler/subword-memory-uncached.json"
  graph Airbender.Compiler.FunctionalNative.SubwordMemoryUncached.native
  base_model Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native
  typing Airbender.Compiler.ConsumerNative.SubwordMemoryUncached.native.typing
  lookup_fields Airbender.Compiler.LookupNative.SubwordMemoryUncached.native
  lookup_source Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native
  memory_model Airbender.Compiler.MemoryNative.SubwordMemoryUncached.native
  helper_model Airbender.Compiler.HelperNative.SubwordMemoryUncached.native

theorem timestamp_source_witness {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (baseValue : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.artifact.gates,
      gate.expressionResidual (baseValue ∘ Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.bank.address) = 0) :
    (Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.timestampOutput).value ((native.assignment hom challenges gamma baseValue).value Airbender.Compiler.ConsumerNative.SubwordMemoryUncached.native.typing hom) =
      (Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.timestampTerms hom challenges gamma (native.assignment hom challenges gamma baseValue)).sum :=
  Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.timestampSourceReduction hom challenges gamma
    (native.assignment hom challenges gamma baseValue)
    (native.helperDefined hom challenges gamma baseValue arithmetic)
    (native.helperCopies baseValue arithmetic)
    (by rw [native.assignment_value]; exact Airbender.Compiler.FunctionalNative.SubwordMemoryUncached.native.canonical_lookups hom challenges gamma baseValue)

theorem generic_source_witness {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (baseValue : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.artifact.gates,
      gate.expressionResidual (baseValue ∘ Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.bank.address) = 0) :
    (Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.genericOutput).value ((native.assignment hom challenges gamma baseValue).value Airbender.Compiler.ConsumerNative.SubwordMemoryUncached.native.typing hom) =
      (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.genericSourceTerms hom challenges gamma (native.assignment hom challenges gamma baseValue)).sum :=
  Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.genericSourceReduction hom challenges gamma
    (native.assignment hom challenges gamma baseValue)
    (native.lookupDefined hom challenges gamma baseValue arithmetic)
    (native.lookupCopies baseValue arithmetic)
    (by rw [native.assignment_value]; exact Airbender.Compiler.FunctionalNative.SubwordMemoryUncached.native.canonical_lookups hom challenges gamma baseValue)

theorem range16_source_witness {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (baseValue : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.artifact.gates,
      gate.expressionResidual (baseValue ∘ Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.bank.address) = 0) :
    (Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.range16Output).value ((native.assignment hom challenges gamma baseValue).value Airbender.Compiler.ConsumerNative.SubwordMemoryUncached.native.typing hom) =
      (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.range16SourceTerms hom challenges gamma (native.assignment hom challenges gamma baseValue)).sum :=
  Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.range16SourceReduction hom challenges gamma
    (native.assignment hom challenges gamma baseValue)
    (native.lookupDefined hom challenges gamma baseValue arithmetic)
    (native.lookupCopies baseValue arithmetic)
    (by rw [native.assignment_value]; exact Airbender.Compiler.FunctionalNative.SubwordMemoryUncached.native.canonical_lookups hom challenges gamma baseValue)

theorem memoryRead_source_witness {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (baseValue : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.artifact.gates,
      gate.expressionResidual (baseValue ∘ Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.bank.address) = 0) :
    ((native.assignment hom challenges gamma baseValue).value Airbender.Compiler.ConsumerNative.SubwordMemoryUncached.native.typing hom) (GKRAddress.InnerLayer 4 2) =
      maskProduct (hom (Airbender.Compiler.MemoryNative.SubwordMemoryUncached.native.sourceExecute.value (Airbender.Compiler.MemoryNative.SubwordMemoryUncached.native.sourceValues baseValue)))
      (Airbender.Compiler.MemoryNative.SubwordMemoryUncached.native.memoryReadTerms hom challenges (native.assignment hom challenges gamma baseValue)).prod :=
  Airbender.Compiler.MemoryNative.SubwordMemoryUncached.native.memoryReadSourceReduction hom challenges
    (native.assignment hom challenges gamma baseValue)
    (native.memoryDefined hom challenges gamma baseValue arithmetic)
    (native.memoryCopies baseValue arithmetic)
    (by rw [native.assignment_value]; exact Airbender.Compiler.FunctionalNative.SubwordMemoryUncached.native.canonical_products hom challenges gamma baseValue)

theorem memoryWrite_source_witness {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (baseValue : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.artifact.gates,
      gate.expressionResidual (baseValue ∘ Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.bank.address) = 0) :
    ((native.assignment hom challenges gamma baseValue).value Airbender.Compiler.ConsumerNative.SubwordMemoryUncached.native.typing hom) (GKRAddress.InnerLayer 4 3) =
      maskProduct (hom (Airbender.Compiler.MemoryNative.SubwordMemoryUncached.native.sourceExecute.value (Airbender.Compiler.MemoryNative.SubwordMemoryUncached.native.sourceValues baseValue)))
      (Airbender.Compiler.MemoryNative.SubwordMemoryUncached.native.memoryWriteTerms hom challenges (native.assignment hom challenges gamma baseValue)).prod :=
  Airbender.Compiler.MemoryNative.SubwordMemoryUncached.native.memoryWriteSourceReduction hom challenges
    (native.assignment hom challenges gamma baseValue)
    (native.memoryDefined hom challenges gamma baseValue arithmetic)
    (native.memoryCopies baseValue arithmetic)
    (by rw [native.assignment_value]; exact Airbender.Compiler.FunctionalNative.SubwordMemoryUncached.native.canonical_products hom challenges gamma baseValue)

end Airbender.Compiler.FunctionalLinksNative.SubwordMemoryUncached
