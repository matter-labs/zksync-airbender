import Airbender.Proofs.GKRProtocol.ProgramDecoderNative.ShiftBinopUncached
import Airbender.Proofs.GKRProtocol.ProgramNativeTransport.ShiftBinopUncached
import Airbender.Proofs.GKRProtocol.NativePublicDecoder

namespace Airbender.Compiler.ProgramDecoderLookup.ShiftBinopUncached
open Airbender Airbender.Compiler Airbender.Trace.NativeDecoder NativeProgramSetup
set_option warningAsError true
set_option Elab.async false

/-- Exact native matching and arithmetic derive the public decoder lookup. -/
theorem decoder_lookup
    {config : ProgramRows.Config} {initial : Reference.RiscV.Sail.State}
    {text : List (BitVec 32)} {capacity : Nat} {masks : Trace.PooledFamily → ProgramRows.Mask}
    {columns : Trace.PooledFamily → List (List Source.BaseField)}
    (setup : UnrolledProgramSetup config initial text capacity masks columns)
    (input : Airbender.Compiler.PooledRowNative.ShiftBinopUncached.Input)
    (arguments : Airbender.Compiler.PooledRowNative.ShiftBinopUncached.LookupArgumentsWith
      (fun group index => unrolledLookupRows initial columns .shiftBinopUncached group index.val) input)
    (typed : (Airbender.Compiler.PooledRowNative.ShiftBinopUncached.inputRow input).decoderQuery[0].val < 65536) : ProgramRows.maskRow (masks .shiftBinop) (Airbender.Compiler.PooledRowNative.ShiftBinopUncached.inputRow input).decoderQuery ∈ columns .shiftBinop := by
  obtain ⟨index, equal⟩ := Airbender.Compiler.PooledRowNative.ShiftBinopUncached.source_member_with
    (fun group index => unrolledLookupRows initial columns .shiftBinopUncached group index.val)
    input arguments 0 (Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.query10.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.ShiftBinopUncached.native.sourcePlacement))
    (ProgramDecoderNative.ShiftBinopUncached.decoder_member input)
    (ProgramDecoderNative.ShiftBinopUncached.decoder_enabled input)
  have matched : Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.query10.fields.map (fun field => field.value ((input.physical ∘ Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.ShiftBinopUncached.native.sourcePlacement)) = unrolledLookupRows initial columns .shiftBinopUncached 0 index.val := equal
  apply NativeProgramSetup.unrolled_decoder_lookup setup .shiftBinopUncached .shiftBinop _
    rfl rfl index.val _ typed
  rw [NativeProgramSetup.unrolled_mask_eq setup .shiftBinop]
  exact (ProgramDecoderNative.ShiftBinopUncached.decoder_tuple input).symm.trans matched

end Airbender.Compiler.ProgramDecoderLookup.ShiftBinopUncached
