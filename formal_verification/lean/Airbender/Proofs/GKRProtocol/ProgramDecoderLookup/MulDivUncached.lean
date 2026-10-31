import Airbender.Proofs.GKRProtocol.ProgramDecoderNative.MulDivUncached
import Airbender.Proofs.GKRProtocol.LogicalRows.MulDivUncached
import Airbender.Proofs.GKRProtocol.NativePublicDecoder

namespace Airbender.Compiler.ProgramDecoderLookup.MulDivUncached
open Airbender Airbender.Compiler Airbender.Trace.NativeDecoder NativeProgramSetup
set_option warningAsError true
set_option Elab.async false

/-- Exact native matching and arithmetic derive the public decoder lookup. -/
theorem decoder_lookup
    {config : ProgramRows.Config} {initial : Reference.RiscV.Sail.State}
    {text : List (BitVec 32)} {capacity : Nat} {masks : Trace.PooledFamily → ProgramRows.Mask}
    {columns : Trace.PooledFamily → List (List Source.BaseField)}
    (setup : UnrolledProgramSetup config initial text capacity masks columns)
    (input : Airbender.Compiler.PooledRowNative.MulDivUncached.Input)
    (arguments : Airbender.Compiler.PooledRowNative.MulDivUncached.LookupArgumentsWith
      (fun group index => unrolledLookupRows initial columns .mulDivUncached group index.val) input)
    (typed : (Airbender.Compiler.PooledRowNative.MulDivUncached.inputRow input).decoderQuery[0].val < 65536) : ProgramRows.maskRow (masks .mulDiv) (Airbender.Compiler.PooledRowNative.MulDivUncached.inputRow input).decoderQuery ∈ columns .mulDiv := by
  obtain ⟨index, equal⟩ := Airbender.Compiler.PooledRowNative.MulDivUncached.source_member_with
    (fun group index => unrolledLookupRows initial columns .mulDivUncached group index.val)
    input arguments 0 (Airbender.Compiler.LookupSourceNative.MulDivUncached.native.query16.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.MulDivUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivUncached.native.sourcePlacement))
    (ProgramDecoderNative.MulDivUncached.decoder_member input)
    (ProgramDecoderNative.MulDivUncached.decoder_enabled input)
  have matched : Airbender.Compiler.LookupSourceNative.MulDivUncached.native.query16.fields.map (fun field => field.value ((input.physical ∘ Airbender.Compiler.LookupSourceNative.MulDivUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivUncached.native.sourcePlacement)) = unrolledLookupRows initial columns .mulDivUncached 0 index.val := equal
  apply NativeProgramSetup.unrolled_decoder_lookup setup .mulDivUncached .mulDiv _
    rfl rfl index.val _ typed
  rw [NativeProgramSetup.unrolled_mask_eq setup .mulDiv]
  exact (ProgramDecoderNative.MulDivUncached.decoder_tuple input).symm.trans matched

end Airbender.Compiler.ProgramDecoderLookup.MulDivUncached
