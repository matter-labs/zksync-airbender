import Airbender.Proofs.GKRProtocol.ProgramDecoderNative.WordMemoryCached
import Airbender.Proofs.GKRProtocol.ProgramNativeTransport.WordMemoryCached
import Airbender.Proofs.GKRProtocol.NativePublicDecoder

namespace Airbender.Compiler.ProgramDecoderLookup.WordMemoryCached
open Airbender Airbender.Compiler Airbender.Trace.NativeDecoder NativeProgramSetup
set_option warningAsError true
set_option Elab.async false

/-- Exact native matching and arithmetic derive the public decoder lookup. -/
theorem decoder_lookup
    {config : ProgramRows.Config} {initial : Reference.RiscV.Sail.State}
    {text : List (BitVec 32)} {capacity : Nat} {masks : Trace.PooledFamily → ProgramRows.Mask}
    {columns : Trace.PooledFamily → List (List Source.BaseField)}
    (setup : UnrolledProgramSetup config initial text capacity masks columns)
    (input : Airbender.Compiler.PooledRowNative.WordMemoryCached.Input)
    (arguments : Airbender.Compiler.PooledRowNative.WordMemoryCached.LookupArgumentsWith
      (fun group index => unrolledLookupRows initial columns .wordMemoryCached group index.val) input)
    (typed : (Airbender.Compiler.PooledRowNative.WordMemoryCached.inputRow input).decoderQuery[0].val < 65536) : ProgramRows.maskRow (masks .wordMemory) (Airbender.Compiler.PooledRowNative.WordMemoryCached.inputRow input).decoderQuery ∈ columns .wordMemory := by
  obtain ⟨index, equal⟩ := Airbender.Compiler.PooledRowNative.WordMemoryCached.source_member_with
    (fun group index => unrolledLookupRows initial columns .wordMemoryCached group index.val)
    input arguments 0 (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.query10.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement))
    (ProgramDecoderNative.WordMemoryCached.decoder_member input)
    (ProgramDecoderNative.WordMemoryCached.decoder_enabled input)
  have matched : Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.query10.fields.map (fun field => field.value ((input.physical ∘ Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement)) = unrolledLookupRows initial columns .wordMemoryCached 0 index.val := equal
  apply NativeProgramSetup.unrolled_decoder_lookup setup .wordMemoryCached .wordMemory _
    rfl rfl index.val _ typed
  rw [NativeProgramSetup.unrolled_mask_eq setup .wordMemory]
  exact (ProgramDecoderNative.WordMemoryCached.decoder_tuple input).symm.trans matched

end Airbender.Compiler.ProgramDecoderLookup.WordMemoryCached
