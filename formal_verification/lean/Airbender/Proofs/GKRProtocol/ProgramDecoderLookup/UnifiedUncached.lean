import Airbender.Proofs.GKRProtocol.ProgramDecoderNative.UnifiedUncached
import Airbender.Proofs.GKRProtocol.LogicalRows.UnifiedUncached
import Airbender.Proofs.GKRProtocol.NativePublicDecoder

namespace Airbender.Compiler.ProgramDecoderLookup.UnifiedUncached
open Airbender Airbender.Compiler Airbender.Trace.NativeDecoder NativeProgramSetup
set_option warningAsError true
set_option Elab.async false

/-- Exact native matching and arithmetic derive the public decoder lookup. -/
theorem decoder_lookup
    {initial : Reference.RiscV.Sail.State} {text : List (BitVec 32)} {capacity : Nat}
    {mask : ProgramRows.Mask} {columns : List (List Source.BaseField)}
    (setup : UnifiedProgramSetup initial text capacity mask columns)
    (input : Airbender.Compiler.UnifiedRowNative.UnifiedUncached.Input)
    (arguments : Airbender.Compiler.UnifiedRowNative.UnifiedUncached.LookupArgumentsWith
      (fun group index => unifiedLookupRows initial columns .unifiedUncached group index.val) input)
    (typed : (Airbender.Compiler.UnifiedRowNative.UnifiedUncached.inputRow input).decoderQuery[0].val < 65536) : ProgramRows.maskRow mask (Airbender.Compiler.UnifiedRowNative.UnifiedUncached.inputRow input).decoderQuery ∈ columns := by
  obtain ⟨index, equal⟩ := Airbender.Compiler.UnifiedRowNative.UnifiedUncached.source_member_with
    (fun group index => unifiedLookupRows initial columns .unifiedUncached group index.val)
    input arguments 0 (Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.query20.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedUncached.native.sourcePlacement))
    (ProgramDecoderNative.UnifiedUncached.decoder_member input)
    (ProgramDecoderNative.UnifiedUncached.decoder_enabled input)
  have matched : Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.query20.fields.map (fun field => field.value ((input.physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedUncached.native.sourcePlacement)) = unifiedLookupRows initial columns .unifiedUncached 0 index.val := equal
  apply NativeProgramSetup.unified_decoder_lookup setup .unifiedUncached _
    (Or.inl rfl) rfl index.val _ typed
  rw [NativeProgramSetup.unified_mask_eq setup]
  exact (ProgramDecoderNative.UnifiedUncached.decoder_tuple input).symm.trans matched

end Airbender.Compiler.ProgramDecoderLookup.UnifiedUncached
