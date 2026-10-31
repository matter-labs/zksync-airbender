import Airbender.Proofs.GKRProtocol.ProgramDecoderNative.SubwordMemoryCached
import Airbender.Proofs.GKRProtocol.LogicalRows.SubwordMemoryCached
import Airbender.Proofs.GKRProtocol.NativePublicDecoder

namespace Airbender.Compiler.ProgramDecoderLookup.SubwordMemoryCached
open Airbender Airbender.Compiler Airbender.Trace.NativeDecoder NativeProgramSetup
set_option warningAsError true
set_option Elab.async false

/-- Exact native matching and arithmetic derive the public decoder lookup. -/
theorem decoder_lookup
    {config : ProgramRows.Config} {initial : Reference.RiscV.Sail.State}
    {text : List (BitVec 32)} {capacity : Nat} {masks : Trace.PooledFamily → ProgramRows.Mask}
    {columns : Trace.PooledFamily → List (List Source.BaseField)}
    (setup : UnrolledProgramSetup config initial text capacity masks columns)
    (input : Airbender.Compiler.PooledRowNative.SubwordMemoryCached.Input)
    (arguments : Airbender.Compiler.PooledRowNative.SubwordMemoryCached.LookupArgumentsWith
      (fun group index => unrolledLookupRows initial columns .subwordMemoryCached group index.val) input)
    (typed : (Airbender.Compiler.PooledRowNative.SubwordMemoryCached.inputRow input).decoderQuery[0].val < 65536) : ProgramRows.maskRow (masks .subwordMemory) (Airbender.Compiler.PooledRowNative.SubwordMemoryCached.inputRow input).decoderQuery ∈ columns .subwordMemory := by
  obtain ⟨index, equal⟩ := Airbender.Compiler.PooledRowNative.SubwordMemoryCached.source_member_with
    (fun group index => unrolledLookupRows initial columns .subwordMemoryCached group index.val)
    input arguments 0 (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.query12.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement))
    (ProgramDecoderNative.SubwordMemoryCached.decoder_member input)
    (ProgramDecoderNative.SubwordMemoryCached.decoder_enabled input)
  have matched : Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.query12.fields.map (fun field => field.value ((input.physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement)) = unrolledLookupRows initial columns .subwordMemoryCached 0 index.val := equal
  apply NativeProgramSetup.unrolled_decoder_lookup setup .subwordMemoryCached .subwordMemory _
    rfl rfl index.val _ typed
  rw [NativeProgramSetup.unrolled_mask_eq setup .subwordMemory]
  exact (ProgramDecoderNative.SubwordMemoryCached.decoder_tuple input).symm.trans matched

end Airbender.Compiler.ProgramDecoderLookup.SubwordMemoryCached
