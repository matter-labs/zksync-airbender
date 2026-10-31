import Airbender.Proofs.GKRProtocol.ProgramDecoderNative.AddSubCached
import Airbender.Proofs.GKRProtocol.ProgramNativeTransport.AddSubCached
import Airbender.Proofs.GKRProtocol.NativePublicDecoder

namespace Airbender.Compiler.ProgramDecoderLookup.AddSubCached
open Airbender Airbender.Compiler Airbender.Trace.NativeDecoder NativeProgramSetup
set_option warningAsError true
set_option Elab.async false

/-- Exact native matching and arithmetic derive the public decoder lookup. -/
theorem decoder_lookup
    {config : ProgramRows.Config} {initial : Reference.RiscV.Sail.State}
    {text : List (BitVec 32)} {capacity : Nat} {masks : Trace.PooledFamily → ProgramRows.Mask}
    {columns : Trace.PooledFamily → List (List Source.BaseField)}
    (setup : UnrolledProgramSetup config initial text capacity masks columns)
    (input : Airbender.Compiler.PooledRowNative.AddSubCached.Input)
    (arguments : Airbender.Compiler.PooledRowNative.AddSubCached.LookupArgumentsWith
      (fun group index => unrolledLookupRows initial columns .addSubCached group index.val) input)
    (typed : (Airbender.Compiler.PooledRowNative.AddSubCached.inputRow input).decoderQuery[0].val < 65536) : ProgramRows.maskRow (masks .addSub) (Airbender.Compiler.PooledRowNative.AddSubCached.inputRow input).decoderQuery ∈ columns .addSub := by
  obtain ⟨index, equal⟩ := Airbender.Compiler.PooledRowNative.AddSubCached.source_member_with
    (fun group index => unrolledLookupRows initial columns .addSubCached group index.val)
    input arguments 0 (Airbender.Compiler.LookupSourceNative.AddSubCached.native.query14.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement))
    (ProgramDecoderNative.AddSubCached.decoder_member input)
    (ProgramDecoderNative.AddSubCached.decoder_enabled input)
  have matched : Airbender.Compiler.LookupSourceNative.AddSubCached.native.query14.fields.map (fun field => field.value ((input.physical ∘ Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement)) = unrolledLookupRows initial columns .addSubCached 0 index.val := equal
  apply NativeProgramSetup.unrolled_decoder_lookup setup .addSubCached .addSub _
    rfl rfl index.val _ typed
  rw [NativeProgramSetup.unrolled_mask_eq setup .addSub]
  exact (ProgramDecoderNative.AddSubCached.decoder_tuple input).symm.trans matched

end Airbender.Compiler.ProgramDecoderLookup.AddSubCached
