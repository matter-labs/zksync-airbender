import Airbender.Proofs.GKRProtocol.ProgramDecoderNative.UnifiedCached
import Airbender.Proofs.GKRProtocol.ProgramNativeTransport.UnifiedCached
import Airbender.Proofs.GKRProtocol.NativePublicDecoder

namespace Airbender.Compiler.ProgramDecoderLookup.UnifiedCached
open Airbender Airbender.Compiler Airbender.Trace.NativeDecoder NativeProgramSetup
set_option warningAsError true
set_option Elab.async false

/-- Exact native matching and arithmetic derive the public decoder lookup. -/
theorem decoder_lookup
    {initial : Reference.RiscV.Sail.State} {text : List (BitVec 32)} {capacity : Nat}
    {mask : ProgramRows.Mask} {columns : List (List Source.BaseField)}
    (setup : UnifiedProgramSetup initial text capacity mask columns)
    (input : Airbender.Compiler.UnifiedRowNative.UnifiedCached.Input)
    (arguments : Airbender.Compiler.UnifiedRowNative.UnifiedCached.LookupArgumentsWith
      (fun group index => unifiedLookupRows initial columns .unifiedCached group index.val) input)
    (typed : (Airbender.Compiler.UnifiedRowNative.UnifiedCached.inputRow input).decoderQuery[0].val < 65536) : ProgramRows.maskRow mask (Airbender.Compiler.UnifiedRowNative.UnifiedCached.inputRow input).decoderQuery ∈ columns := by
  obtain ⟨index, equal⟩ := Airbender.Compiler.UnifiedRowNative.UnifiedCached.source_member_with
    (fun group index => unifiedLookupRows initial columns .unifiedCached group index.val)
    input arguments 0 (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.query20.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement))
    (ProgramDecoderNative.UnifiedCached.decoder_member input)
    (ProgramDecoderNative.UnifiedCached.decoder_enabled input)
  have matched : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.query20.fields.map (fun field => field.value ((input.physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement)) = unifiedLookupRows initial columns .unifiedCached 0 index.val := equal
  apply NativeProgramSetup.unified_decoder_lookup setup .unifiedCached _
    (Or.inr rfl) rfl index.val _ typed
  rw [NativeProgramSetup.unified_mask_eq setup]
  exact (ProgramDecoderNative.UnifiedCached.decoder_tuple input).symm.trans matched

end Airbender.Compiler.ProgramDecoderLookup.UnifiedCached
