import Airbender.Proofs.GKRProtocol.ProgramDecoderNative.JumpBranchCached
import Airbender.Proofs.GKRProtocol.ProgramNativeTransport.JumpBranchCached
import Airbender.Proofs.GKRProtocol.NativePublicDecoder

namespace Airbender.Compiler.ProgramDecoderLookup.JumpBranchCached
open Airbender Airbender.Compiler Airbender.Trace.NativeDecoder NativeProgramSetup
set_option warningAsError true
set_option Elab.async false

/-- Exact native matching and arithmetic derive the public decoder lookup. -/
theorem decoder_lookup
    {config : ProgramRows.Config} {initial : Reference.RiscV.Sail.State}
    {text : List (BitVec 32)} {capacity : Nat} {masks : Trace.PooledFamily → ProgramRows.Mask}
    {columns : Trace.PooledFamily → List (List Source.BaseField)}
    (setup : UnrolledProgramSetup config initial text capacity masks columns)
    (input : Airbender.Compiler.PooledRowNative.JumpBranchCached.Input)
    (arguments : Airbender.Compiler.PooledRowNative.JumpBranchCached.LookupArgumentsWith
      (fun group index => unrolledLookupRows initial columns .jumpBranchCached group index.val) input)
    (typed : (Airbender.Compiler.PooledRowNative.JumpBranchCached.inputRow input).decoderQuery[0].val < 65536) : ProgramRows.maskRow (masks .jumpBranchSlt) (Airbender.Compiler.PooledRowNative.JumpBranchCached.inputRow input).decoderQuery ∈ columns .jumpBranchSlt := by
  obtain ⟨index, equal⟩ := Airbender.Compiler.PooledRowNative.JumpBranchCached.source_member_with
    (fun group index => unrolledLookupRows initial columns .jumpBranchCached group index.val)
    input arguments 0 (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.query12.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.JumpBranchCached.native.sourcePlacement))
    (ProgramDecoderNative.JumpBranchCached.decoder_member input)
    (ProgramDecoderNative.JumpBranchCached.decoder_enabled input)
  have matched : Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.query12.fields.map (fun field => field.value ((input.physical ∘ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.JumpBranchCached.native.sourcePlacement)) = unrolledLookupRows initial columns .jumpBranchCached 0 index.val := equal
  apply NativeProgramSetup.unrolled_decoder_lookup setup .jumpBranchCached .jumpBranchSlt _
    rfl rfl index.val _ typed
  rw [NativeProgramSetup.unrolled_mask_eq setup .jumpBranchSlt]
  exact (ProgramDecoderNative.JumpBranchCached.decoder_tuple input).symm.trans matched

end Airbender.Compiler.ProgramDecoderLookup.JumpBranchCached
