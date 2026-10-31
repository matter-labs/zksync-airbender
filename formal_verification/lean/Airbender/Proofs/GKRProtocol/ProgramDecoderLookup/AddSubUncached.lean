import Airbender.Proofs.GKRProtocol.ProgramDecoderNative.AddSubUncached
import Airbender.Proofs.GKRProtocol.ProgramNativeTransport.AddSubUncached
import Airbender.Proofs.GKRProtocol.NativePublicDecoder

namespace Airbender.Compiler.ProgramDecoderLookup.AddSubUncached
open Airbender Airbender.Compiler Airbender.Trace.NativeDecoder NativeProgramSetup
set_option warningAsError true
set_option Elab.async false

/-- Exact native matching and arithmetic derive the public decoder lookup. -/
theorem decoder_lookup
    {config : ProgramRows.Config} {initial : Reference.RiscV.Sail.State}
    {text : List (BitVec 32)} {capacity : Nat} {masks : Trace.PooledFamily → ProgramRows.Mask}
    {columns : Trace.PooledFamily → List (List Source.BaseField)}
    (setup : UnrolledProgramSetup config initial text capacity masks columns)
    (input : Airbender.Compiler.PooledRowNative.AddSubUncached.Input)
    (arguments : Airbender.Compiler.PooledRowNative.AddSubUncached.LookupArgumentsWith
      (fun group index => unrolledLookupRows initial columns .addSubUncached group index.val) input)
    (typed : (Airbender.Compiler.PooledRowNative.AddSubUncached.inputRow input).decoderQuery[0].val < 65536) : ProgramRows.maskRow (masks .addSub) (Airbender.Compiler.PooledRowNative.AddSubUncached.inputRow input).decoderQuery ∈ columns .addSub := by
  obtain ⟨index, equal⟩ := Airbender.Compiler.PooledRowNative.AddSubUncached.source_member_with
    (fun group index => unrolledLookupRows initial columns .addSubUncached group index.val)
    input arguments 0 (Airbender.Compiler.LookupSourceNative.AddSubUncached.native.query14.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.AddSubUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.AddSubUncached.native.sourcePlacement))
    (ProgramDecoderNative.AddSubUncached.decoder_member input)
    (ProgramDecoderNative.AddSubUncached.decoder_enabled input)
  have matched : Airbender.Compiler.LookupSourceNative.AddSubUncached.native.query14.fields.map (fun field => field.value ((input.physical ∘ Airbender.Compiler.LookupSourceNative.AddSubUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.AddSubUncached.native.sourcePlacement)) = unrolledLookupRows initial columns .addSubUncached 0 index.val := equal
  apply NativeProgramSetup.unrolled_decoder_lookup setup .addSubUncached .addSub _
    rfl rfl index.val _ typed
  rw [NativeProgramSetup.unrolled_mask_eq setup .addSub]
  exact (ProgramDecoderNative.AddSubUncached.decoder_tuple input).symm.trans matched

end Airbender.Compiler.ProgramDecoderLookup.AddSubUncached
