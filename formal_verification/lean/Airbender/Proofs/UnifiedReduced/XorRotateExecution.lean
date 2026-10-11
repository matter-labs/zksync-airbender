import Airbender.Proofs.UnifiedReduced.XorRotateNative

namespace Airbender.UnifiedReduced.Proofs
open Arithmetic Reference.RiscV Reference.RiscV.Sail Reference.Sail Trace Trace.Proofs
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

theorem xorrot_execution [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    (byteInverse : 256 * (-7864320 : ZMod p) = 1)
    {trace : UnifiedTrace p} {initial : State} {cells : List Cell} {program : List ProgramEntry}
    (accepted : Accepted trace) (decoded : Decoded trace program)
    (inputs : NativeInputs customDecoderFields trace initial cells program)
    (setup : trace.rom = Setup.table initial)
    {w : Nat → ZMod p} (member : (⟨.machine, w⟩ : Row p UnifiedFamily) ∈ trace.rows)
    {before after : State} {input : XorRotate.Input} {entry : ProgramEntry}
    (words : XorRotate.WordMapping input ⟨Control.destination w, Control.finalPC w⟩ w)
    (atRow : input.before = retiredState before (Control.initialPC w).toBitVec)
    (position : RowPosition trace initial cells ⟨.machine, w⟩ input.before)
    (present : entry ∈ program) (query : decoderQuery w = entry.query)
    (encoding : entry.instruction = XorRotate.instruction input)
    (history : SailHistory cells (rowEvents trace.memoryEpoch (⟨.machine, w⟩ : Row p UnifiedFamily)).reverse before after) :
    run (normalStep (XorRotate.execution input)) (retiredState before (Control.initialPC w).toBitVec) =
      .ok SailRV32.Functions.RETIRE_SUCCESS (retiredState after (Control.finalPC w).toBitVec) := by
  have result := native_xorrot_soundness hp clockInverse byteInverse trace initial cells program input
    ⟨Control.destination w, Control.finalPC w⟩ w
    ⟨⟨inputs, setup⟩, ⟨accepted, decoded, member⟩, ⟨words, position, entry, present, query, encoding⟩⟩
  obtain ⟨addresses, image⟩ := inputs.programImage
  have fields := (run_program_sources image entry present).fields
  have metadata := xorrot_metadata fields encoding
  have core := Verification.holds_of_sublist (accepted.constraints _ member)
    (List.sublist_append_left (importedConstraints trace.rom) importedConstraintsTimestampLookups)
  have decoderSize : 524288 < p := by dsimp [timestampBase] at hp; omega
  have noStore : w 29 = 0 := by
    have flag := decoder_selectors decoderSize core (custom_field_bounds fields).2.1 query 18
    rw [metadata.1] at flag
    simpa [importedConstraintsDecoderColumns, Nat.testBit, Nat.shiftRight_eq_div_pow] using flag
  have indices := native_query_indices (by dsimp [limbBase]; omega) query
  obtain ⟨final, normal, projected⟩ := result
  have effects := register_effects core noStore indices.2.2 trace.memoryEpoch
    ⟨Control.destination w, Control.finalPC w⟩ rfl history
  have destination : (.Regidx entry.data.rd : SailRV32.regidx) = input.rd := by rw [metadata.1]
  rw [destination] at effects
  rw [atRow] at projected normal
  have same := (EStateM.Result.ok.inj (projected.symm.trans effects)).2
  simpa only [same] using normal

end Airbender.UnifiedReduced.Proofs
