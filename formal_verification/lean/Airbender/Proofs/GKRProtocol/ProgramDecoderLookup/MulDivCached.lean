import Airbender.Proofs.GKRProtocol.ProgramDecoderNative.MulDivCached
import Airbender.Proofs.GKRProtocol.ProgramNativeTransport.MulDivCached
import Airbender.Proofs.GKRProtocol.NativePublicDecoder

namespace Airbender.Compiler.ProgramDecoderLookup.MulDivCached
open Airbender Airbender.Compiler Airbender.Trace.NativeDecoder NativeProgramSetup
set_option warningAsError true
set_option Elab.async false

/-- Exact native matching and arithmetic derive the public decoder lookup. -/
theorem decoder_lookup
    {config : ProgramRows.Config} {initial : Reference.RiscV.Sail.State}
    {text : List (BitVec 32)} {capacity : Nat} {masks : Trace.PooledFamily → ProgramRows.Mask}
    {columns : Trace.PooledFamily → List (List Source.BaseField)}
    (setup : UnrolledProgramSetup config initial text capacity masks columns)
    (input : Airbender.Compiler.PooledRowNative.MulDivCached.Input)
    (arguments : Airbender.Compiler.PooledRowNative.MulDivCached.LookupArgumentsWith
      (fun group index => unrolledLookupRows initial columns .mulDivCached group index.val) input)
    (typed : (Airbender.Compiler.PooledRowNative.MulDivCached.inputRow input).decoderQuery[0].val < 65536) : ProgramRows.maskRow (masks .mulDiv) (Airbender.Compiler.PooledRowNative.MulDivCached.inputRow input).decoderQuery ∈ columns .mulDiv := by
  obtain ⟨index, equal⟩ := Airbender.Compiler.PooledRowNative.MulDivCached.source_member_with
    (fun group index => unrolledLookupRows initial columns .mulDivCached group index.val)
    input arguments 0 (Airbender.Compiler.LookupSourceNative.MulDivCached.native.query16.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement))
    (ProgramDecoderNative.MulDivCached.decoder_member input)
    (ProgramDecoderNative.MulDivCached.decoder_enabled input)
  have matched : Airbender.Compiler.LookupSourceNative.MulDivCached.native.query16.fields.map (fun field => field.value ((input.physical ∘ Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement)) = unrolledLookupRows initial columns .mulDivCached 0 index.val := equal
  apply NativeProgramSetup.unrolled_decoder_lookup setup .mulDivCached .mulDiv _
    rfl rfl index.val _ typed
  rw [NativeProgramSetup.unrolled_mask_eq setup .mulDiv]
  exact (ProgramDecoderNative.MulDivCached.decoder_tuple input).symm.trans matched

end Airbender.Compiler.ProgramDecoderLookup.MulDivCached
