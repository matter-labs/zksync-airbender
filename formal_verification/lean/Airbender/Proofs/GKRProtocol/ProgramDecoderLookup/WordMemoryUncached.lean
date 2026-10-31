import Airbender.Proofs.GKRProtocol.ProgramDecoderNative.WordMemoryUncached
import Airbender.Proofs.GKRProtocol.LogicalRows.WordMemoryUncached
import Airbender.Proofs.GKRProtocol.NativePublicDecoder

namespace Airbender.Compiler.ProgramDecoderLookup.WordMemoryUncached
open Airbender Airbender.Compiler Airbender.Trace.NativeDecoder NativeProgramSetup
set_option warningAsError true
set_option Elab.async false

/-- Exact native matching and arithmetic derive the public decoder lookup. -/
theorem decoder_lookup
    {config : ProgramRows.Config} {initial : Reference.RiscV.Sail.State}
    {text : List (BitVec 32)} {capacity : Nat} {masks : Trace.PooledFamily → ProgramRows.Mask}
    {columns : Trace.PooledFamily → List (List Source.BaseField)}
    (setup : UnrolledProgramSetup config initial text capacity masks columns)
    (input : Airbender.Compiler.PooledRowNative.WordMemoryUncached.Input)
    (arguments : Airbender.Compiler.PooledRowNative.WordMemoryUncached.LookupArgumentsWith
      (fun group index => unrolledLookupRows initial columns .wordMemoryUncached group index.val) input)
    (typed : (Airbender.Compiler.PooledRowNative.WordMemoryUncached.inputRow input).decoderQuery[0].val < 65536) : ProgramRows.maskRow (masks .wordMemory) (Airbender.Compiler.PooledRowNative.WordMemoryUncached.inputRow input).decoderQuery ∈ columns .wordMemory := by
  obtain ⟨index, equal⟩ := Airbender.Compiler.PooledRowNative.WordMemoryUncached.source_member_with
    (fun group index => unrolledLookupRows initial columns .wordMemoryUncached group index.val)
    input arguments 0 (Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.query10.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.WordMemoryUncached.native.sourcePlacement))
    (ProgramDecoderNative.WordMemoryUncached.decoder_member input)
    (ProgramDecoderNative.WordMemoryUncached.decoder_enabled input)
  have matched : Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.query10.fields.map (fun field => field.value ((input.physical ∘ Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.WordMemoryUncached.native.sourcePlacement)) = unrolledLookupRows initial columns .wordMemoryUncached 0 index.val := equal
  apply NativeProgramSetup.unrolled_decoder_lookup setup .wordMemoryUncached .wordMemory _
    rfl rfl index.val _ typed
  rw [NativeProgramSetup.unrolled_mask_eq setup .wordMemory]
  exact (ProgramDecoderNative.WordMemoryUncached.decoder_tuple input).symm.trans matched

end Airbender.Compiler.ProgramDecoderLookup.WordMemoryUncached
