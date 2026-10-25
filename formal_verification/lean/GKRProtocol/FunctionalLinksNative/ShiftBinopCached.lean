import GKRProtocol.FunctionalLinksImport
import GKRProtocol.FunctionalNative.ShiftBinopCached
import GKRProtocol.LookupSourceNative.ShiftBinopCached
import GKRProtocol.MemoryNative.ShiftBinopCached
import GKRProtocol.HelperNative.ShiftBinopCached

namespace Airbender.Compiler.FunctionalLinksNative.ShiftBinopCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_functional_links native from "artifacts/compiler/shift-binop-cached.json"
  graph Airbender.Compiler.FunctionalNative.ShiftBinopCached.native
  base_model Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native
  typing Airbender.Compiler.ConsumerNative.ShiftBinopCached.native.typing
  lookup_fields Airbender.Compiler.LookupNative.ShiftBinopCached.native
  lookup_source Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native
  memory_model Airbender.Compiler.MemoryNative.ShiftBinopCached.native
  helper_model Airbender.Compiler.HelperNative.ShiftBinopCached.native

theorem timestamp_source_witness {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (baseValue : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.artifact.gates,
      gate.expressionResidual (baseValue ∘ Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.bank.address) = 0) :
    (Airbender.Compiler.LookupNative.ShiftBinopCached.native.timestampOutput).value ((native.assignment hom challenges gamma baseValue).value Airbender.Compiler.ConsumerNative.ShiftBinopCached.native.typing hom) =
      (Airbender.Compiler.HelperNative.ShiftBinopCached.native.timestampTerms hom challenges gamma (native.assignment hom challenges gamma baseValue)).sum :=
  Airbender.Compiler.HelperNative.ShiftBinopCached.native.timestampSourceReduction hom challenges gamma
    (native.assignment hom challenges gamma baseValue)
    (native.helperDefined hom challenges gamma baseValue arithmetic)
    (native.helperCopies baseValue arithmetic)
    (by rw [native.assignment_value]; exact Airbender.Compiler.FunctionalNative.ShiftBinopCached.native.canonical_lookups hom challenges gamma baseValue)

theorem generic_source_witness {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (baseValue : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.artifact.gates,
      gate.expressionResidual (baseValue ∘ Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.bank.address) = 0) :
    (Airbender.Compiler.LookupNative.ShiftBinopCached.native.genericOutput).value ((native.assignment hom challenges gamma baseValue).value Airbender.Compiler.ConsumerNative.ShiftBinopCached.native.typing hom) =
      (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.genericSourceTerms hom challenges gamma (native.assignment hom challenges gamma baseValue)).sum :=
  Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.genericSourceReduction hom challenges gamma
    (native.assignment hom challenges gamma baseValue)
    (native.lookupDefined hom challenges gamma baseValue arithmetic)
    (native.lookupCopies baseValue arithmetic)
    (by rw [native.assignment_value]; exact Airbender.Compiler.FunctionalNative.ShiftBinopCached.native.canonical_lookups hom challenges gamma baseValue)

theorem range16_source_witness {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (baseValue : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.artifact.gates,
      gate.expressionResidual (baseValue ∘ Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.bank.address) = 0) :
    (Airbender.Compiler.LookupNative.ShiftBinopCached.native.range16Output).value ((native.assignment hom challenges gamma baseValue).value Airbender.Compiler.ConsumerNative.ShiftBinopCached.native.typing hom) =
      (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.range16SourceTerms hom challenges gamma (native.assignment hom challenges gamma baseValue)).sum :=
  Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.range16SourceReduction hom challenges gamma
    (native.assignment hom challenges gamma baseValue)
    (native.lookupDefined hom challenges gamma baseValue arithmetic)
    (native.lookupCopies baseValue arithmetic)
    (by rw [native.assignment_value]; exact Airbender.Compiler.FunctionalNative.ShiftBinopCached.native.canonical_lookups hom challenges gamma baseValue)

theorem memoryRead_source_witness {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (baseValue : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.artifact.gates,
      gate.expressionResidual (baseValue ∘ Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.bank.address) = 0) :
    ((native.assignment hom challenges gamma baseValue).value Airbender.Compiler.ConsumerNative.ShiftBinopCached.native.typing hom) (GKRAddress.InnerLayer 4 4) =
      maskProduct (hom (Airbender.Compiler.MemoryNative.ShiftBinopCached.native.sourceExecute.value (Airbender.Compiler.MemoryNative.ShiftBinopCached.native.sourceValues baseValue)))
      (Airbender.Compiler.MemoryNative.ShiftBinopCached.native.memoryReadTerms hom challenges (native.assignment hom challenges gamma baseValue)).prod :=
  Airbender.Compiler.MemoryNative.ShiftBinopCached.native.memoryReadSourceReduction hom challenges
    (native.assignment hom challenges gamma baseValue)
    (native.memoryDefined hom challenges gamma baseValue arithmetic)
    (native.memoryCopies baseValue arithmetic)
    (by rw [native.assignment_value]; exact Airbender.Compiler.FunctionalNative.ShiftBinopCached.native.canonical_products hom challenges gamma baseValue)

theorem memoryWrite_source_witness {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (baseValue : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.artifact.gates,
      gate.expressionResidual (baseValue ∘ Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.bank.address) = 0) :
    ((native.assignment hom challenges gamma baseValue).value Airbender.Compiler.ConsumerNative.ShiftBinopCached.native.typing hom) (GKRAddress.InnerLayer 4 5) =
      maskProduct (hom (Airbender.Compiler.MemoryNative.ShiftBinopCached.native.sourceExecute.value (Airbender.Compiler.MemoryNative.ShiftBinopCached.native.sourceValues baseValue)))
      (Airbender.Compiler.MemoryNative.ShiftBinopCached.native.memoryWriteTerms hom challenges (native.assignment hom challenges gamma baseValue)).prod :=
  Airbender.Compiler.MemoryNative.ShiftBinopCached.native.memoryWriteSourceReduction hom challenges
    (native.assignment hom challenges gamma baseValue)
    (native.memoryDefined hom challenges gamma baseValue arithmetic)
    (native.memoryCopies baseValue arithmetic)
    (by rw [native.assignment_value]; exact Airbender.Compiler.FunctionalNative.ShiftBinopCached.native.canonical_products hom challenges gamma baseValue)

end Airbender.Compiler.FunctionalLinksNative.ShiftBinopCached
