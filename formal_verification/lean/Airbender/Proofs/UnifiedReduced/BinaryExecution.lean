import Airbender.Proofs.UnifiedReduced.RegisterRetirement
import Airbender.Proofs.UnifiedReduced.BinarySoundness
import Airbender.Proofs.UnifiedReduced.ShiftSoundness

namespace Airbender.UnifiedReduced.Proofs
open Arithmetic Reference.RiscV Reference.RiscV.Sail Reference.Sail Trace Trace.Proofs
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

private theorem binary_metadata {input : Binary.Input} {entry : ProgramEntry} (shift : Bool)
    (encoding : (if shift then Shift.instruction input else Binary.instruction input) = some entry.instruction)
    (fields : decoderFields entry.instruction = some entry.data) :
    entry.data.mask < 262144 ∧ entry.data.rd = match input.rd with | .Regidx bits => bits := by
  rcases input with ⟨op, immediate, left, right, pc, ⟨rs1⟩, ⟨rs2⟩, ⟨rd⟩, imm, state⟩
  change BitVec 5 at rs1 rs2 rd
  cases shift <;> cases op <;> cases immediate
  all_goals simp [Shift.instruction, Binary.instruction] at encoding
  all_goals rw [← encoding] at fields
  all_goals by_cases zero : rd = (0#5)
  all_goals simp [decoderFields, Trace.decoderFields, JumpBranchSlt.decoderFields,
    ShiftBinop.decoderFields, ShiftBinop.instructionFields, binaryFields,
    ShiftBinop.Operation.isShift, ShiftBinop.Operation.tag, DecoderData.mapFamily, zero] at fields
  all_goals try rcases fields with ⟨_, fields⟩
  all_goals rw [← fields]
  all_goals exact ⟨by norm_num, rfl⟩

theorem binary_execution [Fact p.Prime] [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    (hp : 4194304 ≤ p) (inverse : (-3840 : ZMod p) * 524288 = 1)
    (byteInverse : 256 * (-7864320 : ZMod p) = 1) (shift : Bool)
    {trace : UnifiedTrace p} {initial : State} {cells : List Cell} {program : List ProgramEntry}
    (accepted : Accepted trace) (decoded : Decoded trace program)
    {w : Nat → ZMod p} (member : (⟨.machine, w⟩ : Row p UnifiedFamily) ∈ trace.rows)
    {before after : State} {input : Binary.Input} {entry : ProgramEntry}
    (inputs : Binary.InterfaceAssumptions trace initial cells program input ⟨Control.destination w, Control.finalPC w⟩ w)
    (words : Binary.WordMapping input ⟨Control.destination w, Control.finalPC w⟩ w)
    (atRow : input.before = retiredState before (Control.initialPC w).toBitVec)
    (position : RowPosition trace initial cells ⟨.machine, w⟩ input.before)
    (present : entry ∈ program) (query : decoderQuery w = entry.query)
    (encoding : (if shift then Shift.instruction input else Binary.instruction input) = some entry.instruction)
    (history : SailHistory cells (rowEvents trace.memoryEpoch (⟨.machine, w⟩ : Row p UnifiedFamily)).reverse before after) :
    ∃ clause, instructionClause entry.instruction = some clause ∧
      run (normalStep clause) (retiredState before (Control.initialPC w).toBitVec) =
        .ok SailRV32.Functions.RETIRE_SUCCESS (retiredState after (Control.finalPC w).toBitVec) := by
  have clockSize : 2 * timestampBase + 4 < p := by dsimp [timestampBase]; omega
  have result : ShiftBinop.spec input ⟨Control.destination w, Control.finalPC w⟩ := by
    cases choice : shift
    · exact Binary.Proofs.soundness clockSize inverse byteInverse trace initial cells program input
        ⟨Control.destination w, Control.finalPC w⟩ w
        ⟨inputs, ⟨accepted, decoded, member⟩, ⟨words, position, entry, present, query, by simpa [choice] using encoding⟩⟩
    · exact Shift.Proofs.soundness clockSize inverse byteInverse trace initial cells program input
        ⟨Control.destination w, Control.finalPC w⟩ w
        ⟨inputs, ⟨accepted, decoded, member⟩, ⟨words, position, entry, present, query, by simpa [choice] using encoding⟩⟩
  obtain ⟨addresses, image⟩ := inputs.initialization.programImage
  have fields := (run_program_sources image entry present).fields
  have metadata := binary_metadata shift encoding fields
  have core := Verification.holds_of_sublist (accepted.constraints _ member)
    (List.sublist_append_left (importedConstraints trace.rom) importedConstraintsTimestampLookups)
  have spec : stepSpec (retiredState before (Control.initialPC w).toBitVec)
      (ShiftBinop.execution input) input.rd ⟨Control.destination w, Control.finalPC w⟩ := by
    change stepSpec input.before _ _ _ at result
    rw [atRow] at result
    exact result
  refine ⟨ShiftBinop.execution input, ?_,
    register_retirement (by omega) core fields query metadata.1 metadata.2 trace.memoryEpoch history spec⟩
  rcases input with ⟨op, immediate, left, right, pc, rs1, rs2, rd, imm, state⟩
  cases shift <;> cases op <;> cases immediate
  all_goals simp [Shift.instruction, Binary.instruction] at encoding
  all_goals rw [← encoding]
  all_goals rfl

end Airbender.UnifiedReduced.Proofs
