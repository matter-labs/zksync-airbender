import GKRProtocol.FunctionalLinksImport
import GKRProtocol.FunctionalNative.KeccakUncached
import GKRProtocol.LookupSourceNative.KeccakUncached
import GKRProtocol.MemoryNative.KeccakUncached
import GKRProtocol.HelperNative.KeccakUncached

namespace Airbender.Compiler.FunctionalLinksNative.KeccakUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_functional_links native from "artifacts/compiler/keccak-uncached.json"
  graph Airbender.Compiler.FunctionalNative.KeccakUncached.native
  base_model Airbender.Compiler.FullArithmeticNative.KeccakUncached.native
  typing Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing
  lookup_fields Airbender.Compiler.LookupNative.KeccakUncached.native
  lookup_source Airbender.Compiler.LookupSourceNative.KeccakUncached.native
  memory_model Airbender.Compiler.MemoryNative.KeccakUncached.native
  helper_model Airbender.Compiler.HelperNative.KeccakUncached.native

theorem timestamp_source_witness {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (baseValue : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.artifact.gates,
      gate.expressionResidual (baseValue ∘ Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank.address) = 0) :
    (Airbender.Compiler.LookupNative.KeccakUncached.native.timestampOutput).value ((native.assignment hom challenges gamma baseValue).value Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing hom) =
      (Airbender.Compiler.HelperNative.KeccakUncached.native.timestampTerms hom challenges gamma (native.assignment hom challenges gamma baseValue)).sum :=
  Airbender.Compiler.HelperNative.KeccakUncached.native.timestampSourceReduction hom challenges gamma
    (native.assignment hom challenges gamma baseValue)
    (native.helperDefined hom challenges gamma baseValue arithmetic)
    (native.helperCopies baseValue arithmetic)
    (by rw [native.assignment_value]; exact Airbender.Compiler.FunctionalNative.KeccakUncached.native.canonical_lookups hom challenges gamma baseValue)

theorem generic_source_witness {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (baseValue : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.artifact.gates,
      gate.expressionResidual (baseValue ∘ Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank.address) = 0) :
    (Airbender.Compiler.LookupNative.KeccakUncached.native.genericOutput).value ((native.assignment hom challenges gamma baseValue).value Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing hom) =
      (Airbender.Compiler.LookupSourceNative.KeccakUncached.native.genericSourceTerms hom challenges gamma (native.assignment hom challenges gamma baseValue)).sum :=
  Airbender.Compiler.LookupSourceNative.KeccakUncached.native.genericSourceReduction hom challenges gamma
    (native.assignment hom challenges gamma baseValue)
    (native.lookupDefined hom challenges gamma baseValue arithmetic)
    (native.lookupCopies baseValue arithmetic)
    (by rw [native.assignment_value]; exact Airbender.Compiler.FunctionalNative.KeccakUncached.native.canonical_lookups hom challenges gamma baseValue)

theorem memoryRead_source_witness {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (baseValue : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.artifact.gates,
      gate.expressionResidual (baseValue ∘ Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank.address) = 0) :
    ((native.assignment hom challenges gamma baseValue).value Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing hom) (GKRAddress.InnerLayer 6 2) =
      maskProduct (hom (Airbender.Compiler.MemoryNative.KeccakUncached.native.sourceExecute.value (Airbender.Compiler.MemoryNative.KeccakUncached.native.sourceValues baseValue)))
      (Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryReadTerms hom challenges (native.assignment hom challenges gamma baseValue)).prod :=
  Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryReadSourceReduction hom challenges
    (native.assignment hom challenges gamma baseValue)
    (native.memoryDefined hom challenges gamma baseValue arithmetic)
    (native.memoryCopies baseValue arithmetic)
    (by rw [native.assignment_value]; exact Airbender.Compiler.FunctionalNative.KeccakUncached.native.canonical_products hom challenges gamma baseValue)

theorem memoryWrite_source_witness {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (baseValue : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.artifact.gates,
      gate.expressionResidual (baseValue ∘ Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank.address) = 0) :
    ((native.assignment hom challenges gamma baseValue).value Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing hom) (GKRAddress.InnerLayer 6 3) =
      maskProduct (hom (Airbender.Compiler.MemoryNative.KeccakUncached.native.sourceExecute.value (Airbender.Compiler.MemoryNative.KeccakUncached.native.sourceValues baseValue)))
      (Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryWriteTerms hom challenges (native.assignment hom challenges gamma baseValue)).prod :=
  Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryWriteSourceReduction hom challenges
    (native.assignment hom challenges gamma baseValue)
    (native.memoryDefined hom challenges gamma baseValue arithmetic)
    (native.memoryCopies baseValue arithmetic)
    (by rw [native.assignment_value]; exact Airbender.Compiler.FunctionalNative.KeccakUncached.native.canonical_products hom challenges gamma baseValue)

end Airbender.Compiler.FunctionalLinksNative.KeccakUncached
