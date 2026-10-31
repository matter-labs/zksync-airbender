import Airbender.Proofs.GKRProtocol.ProgramDecoderNative.ShiftBinopCached
import Airbender.Proofs.GKRProtocol.LogicalRows.ShiftBinopCached
import Airbender.Proofs.GKRProtocol.NativePublicDecoder

namespace Airbender.Compiler.ProgramDecoderLookup.ShiftBinopCached
open Airbender Airbender.Compiler Airbender.Trace.NativeDecoder NativeProgramSetup
set_option warningAsError true
set_option Elab.async false

/-- Exact native matching and arithmetic derive the public decoder lookup. -/
theorem decoder_lookup
    {config : ProgramRows.Config} {initial : Reference.RiscV.Sail.State}
    {text : List (BitVec 32)} {capacity : Nat} {masks : Trace.PooledFamily → ProgramRows.Mask}
    {columns : Trace.PooledFamily → List (List Source.BaseField)}
    (setup : UnrolledProgramSetup config initial text capacity masks columns)
    (input : Airbender.Compiler.PooledRowNative.ShiftBinopCached.Input)
    (arguments : Airbender.Compiler.PooledRowNative.ShiftBinopCached.LookupArgumentsWith
      (fun group index => unrolledLookupRows initial columns .shiftBinopCached group index.val) input)
    (typed : (Airbender.Compiler.PooledRowNative.ShiftBinopCached.inputRow input).decoderQuery[0].val < 65536) : ProgramRows.maskRow (masks .shiftBinop) (Airbender.Compiler.PooledRowNative.ShiftBinopCached.inputRow input).decoderQuery ∈ columns .shiftBinop := by
  obtain ⟨index, equal⟩ := Airbender.Compiler.PooledRowNative.ShiftBinopCached.source_member_with
    (fun group index => unrolledLookupRows initial columns .shiftBinopCached group index.val)
    input arguments 0 (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.query10.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement))
    (ProgramDecoderNative.ShiftBinopCached.decoder_member input)
    (ProgramDecoderNative.ShiftBinopCached.decoder_enabled input)
  have matched : Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.query10.fields.map (fun field => field.value ((input.physical ∘ Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement)) = unrolledLookupRows initial columns .shiftBinopCached 0 index.val := equal
  apply NativeProgramSetup.unrolled_decoder_lookup setup .shiftBinopCached .shiftBinop _
    rfl rfl index.val _ typed
  rw [NativeProgramSetup.unrolled_mask_eq setup .shiftBinop]
  exact (ProgramDecoderNative.ShiftBinopCached.decoder_tuple input).symm.trans matched

end Airbender.Compiler.ProgramDecoderLookup.ShiftBinopCached
