import Airbender.Proofs.UnifiedReduced.XorRotateNative

namespace Airbender.UnifiedReduced.Proofs
open Arithmetic Reference.RiscV Reference.RiscV.Sail Reference.Sail Trace Trace.Proofs
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

theorem xorrot_execution_from_memory [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    (byteInverse : 256 * (-7864320 : ZMod p) = 1)
    {trace : UnifiedTrace p} {initial : State} {cells : List Cell} {program : List ProgramEntry}
    {projection : SailRV32.instruction → Option (DecoderData UnifiedFamily)}
    (accepted : Accepted trace)
    (inputs : NativeInputs projection trace initial cells program)
    (setup : trace.rom = Setup.table initial)
    {w : Nat → ZMod p} (member : (⟨.machine, w⟩ : Row p UnifiedFamily) ∈ trace.rows)
    {before after : State} {input : XorRotate.Input} {entry : ProgramEntry}
    (words : XorRotate.WordMapping input ⟨Control.destination w, Control.finalPC w⟩ w)
    (atRow : input.before = retiredState before (Control.initialPC w).toBitVec)
    (position : RowPosition trace initial cells ⟨.machine, w⟩ input.before)
    (fields : customDecoderFields entry.instruction = some entry.data)
    (memory : MemoryExecution trace initial cells) (query : decoderQuery w = entry.query)
    (encoding : entry.instruction = XorRotate.instruction input)
    (history : SailHistory cells (rowEvents trace.memoryEpoch (⟨.machine, w⟩ : Row p UnifiedFamily)).reverse before after) :
    run (normalStep (XorRotate.execution input)) (retiredState before (Control.initialPC w).toBitVec) =
      .ok SailRV32.Functions.RETIRE_SUCCESS (retiredState after (Control.finalPC w).toBitVec) := by
  have result := xorrot_soundness_from_memory hp clockInverse byteInverse inputs accepted memory setup member
    words position fields query encoding
  have metadata := xorrot_metadata fields encoding
  have core := Verification.holds_of_sublist (accepted.constraints _ member)
    (List.sublist_append_left (importedConstraints trace.rom) importedConstraintsTimestampLookups)
  have destination : (.Regidx entry.data.rd : SailRV32.regidx) = input.rd := by rw [metadata.1]
  change stepSpec input.before (XorRotate.execution input) input.rd
    ⟨Control.destination w, Control.finalPC w⟩ at result
  rw [atRow] at result
  exact custom_register_retirement (by dsimp [timestampBase] at hp; omega)
    core fields query destination trace.memoryEpoch history result

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
  obtain ⟨addresses, image⟩ := inputs.programImage
  exact xorrot_execution_from_memory hp clockInverse byteInverse accepted inputs setup member words atRow position
    (run_program_sources image entry present).fields
    (custom_memory_execution hp clockInverse accepted inputs decoded) query encoding history

end Airbender.UnifiedReduced.Proofs
