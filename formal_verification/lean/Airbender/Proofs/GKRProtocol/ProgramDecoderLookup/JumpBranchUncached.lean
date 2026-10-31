import Airbender.Proofs.GKRProtocol.ProgramDecoderNative.JumpBranchUncached
import Airbender.Proofs.GKRProtocol.LogicalRows.JumpBranchUncached
import Airbender.Proofs.GKRProtocol.NativePublicDecoder

namespace Airbender.Compiler.ProgramDecoderLookup.JumpBranchUncached
open Airbender Airbender.Compiler Airbender.Trace.NativeDecoder NativeProgramSetup
set_option warningAsError true
set_option Elab.async false

/-- Exact native matching and arithmetic derive the public decoder lookup. -/
theorem decoder_lookup
    {config : ProgramRows.Config} {initial : Reference.RiscV.Sail.State}
    {text : List (BitVec 32)} {capacity : Nat} {masks : Trace.PooledFamily → ProgramRows.Mask}
    {columns : Trace.PooledFamily → List (List Source.BaseField)}
    (setup : UnrolledProgramSetup config initial text capacity masks columns)
    (input : Airbender.Compiler.PooledRowNative.JumpBranchUncached.Input)
    (arguments : Airbender.Compiler.PooledRowNative.JumpBranchUncached.LookupArgumentsWith
      (fun group index => unrolledLookupRows initial columns .jumpBranchUncached group index.val) input)
    (typed : (Airbender.Compiler.PooledRowNative.JumpBranchUncached.inputRow input).decoderQuery[0].val < 65536) : ProgramRows.maskRow (masks .jumpBranchSlt) (Airbender.Compiler.PooledRowNative.JumpBranchUncached.inputRow input).decoderQuery ∈ columns .jumpBranchSlt := by
  obtain ⟨index, equal⟩ := Airbender.Compiler.PooledRowNative.JumpBranchUncached.source_member_with
    (fun group index => unrolledLookupRows initial columns .jumpBranchUncached group index.val)
    input arguments 0 (Airbender.Compiler.LookupSourceNative.JumpBranchUncached.native.query12.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.JumpBranchUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.JumpBranchUncached.native.sourcePlacement))
    (ProgramDecoderNative.JumpBranchUncached.decoder_member input)
    (ProgramDecoderNative.JumpBranchUncached.decoder_enabled input)
  have matched : Airbender.Compiler.LookupSourceNative.JumpBranchUncached.native.query12.fields.map (fun field => field.value ((input.physical ∘ Airbender.Compiler.LookupSourceNative.JumpBranchUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.JumpBranchUncached.native.sourcePlacement)) = unrolledLookupRows initial columns .jumpBranchUncached 0 index.val := equal
  apply NativeProgramSetup.unrolled_decoder_lookup setup .jumpBranchUncached .jumpBranchSlt _
    rfl rfl index.val _ typed
  rw [NativeProgramSetup.unrolled_mask_eq setup .jumpBranchSlt]
  exact (ProgramDecoderNative.JumpBranchUncached.decoder_tuple input).symm.trans matched

end Airbender.Compiler.ProgramDecoderLookup.JumpBranchUncached
