import Airbender.Review.UnifiedReduced.Execution
import Airbender.Proofs.UnifiedReduced.TraceSoundness
import Airbender.Proofs.UnifiedReduced.RegisterRetirement

namespace Airbender.UnifiedReduced.Proofs
open Arithmetic Reference.RiscV Reference.RiscV.Sail Reference.Sail Trace Trace.Proofs
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

def arithmeticInstruction (input : Input) : SailRV32.instruction :=
  match input.row.opcode with
  | .add => .RTYPE (input.rs2, input.rs1, input.rd, .ADD)
  | .addi => .ITYPE (input.encodedImmediate, input.rs1, input.rd, .ADDI)
  | .sub => .RTYPE (input.rs2, input.rs1, input.rd, .SUB)
  | .lui => .UTYPE (input.encodedUpperImmediate, input.rd, .LUI)
  | .auipc => .UTYPE (input.encodedUpperImmediate, input.rd, .AUIPC)

theorem arithmetic_execution [Fact p.Prime] [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    (hp : 4194304 ≤ p) (inverse : (-3840 : ZMod p) * 524288 = 1)
    {trace : UnifiedTrace p} {initial : State} {cells : List Cell} {program : List ProgramEntry}
    (accepted : Accepted trace) (decoded : Decoded trace program)
    (inputs : NativeInputs decoderFields trace initial cells program)
    (registers : ∀ index, Cell.register index ∈ cells)
    {w : Nat → ZMod p} (member : (⟨.machine, w⟩ : Row p UnifiedFamily) ∈ trace.rows)
    {before after : State} {input : Input} {entry : ProgramEntry}
    (words : WordMapping input ⟨Control.destination w, Control.finalPC w⟩ w)
    (atRow : input.before = retiredState before (Control.initialPC w).toBitVec)
    (position : RowPosition trace initial cells ⟨.machine, w⟩ input.before)
    (present : entry ∈ program) (query : decoderQuery w = entry.query)
    (encoding : entry.instruction = arithmeticInstruction input)
    (history : SailHistory cells (rowEvents trace.memoryEpoch (⟨.machine, w⟩ : Row p UnifiedFamily)).reverse before after) :
    ∃ clause, instructionClause entry.instruction = some clause ∧
      run (normalStep clause) (retiredState before (Control.initialPC w).toBitVec) =
        .ok SailRV32.Functions.RETIRE_SUCCESS (retiredState after (Control.finalPC w).toBitVec) := by
  have clockSize : 2 * timestampBase + 4 < p := by dsimp [timestampBase]; omega
  have result := trace_soundness clockSize inverse trace initial cells program input
    ⟨Control.destination w, Control.finalPC w⟩ w
    ⟨⟨inputs, fun index _ => registers index⟩, ⟨accepted, decoded, member⟩,
      ⟨words, position, entry, present, query, encoding⟩⟩
  obtain ⟨addresses, image⟩ := inputs.programImage
  have fields := (run_program_sources image entry present).fields
  have core := Verification.holds_of_sublist (accepted.constraints _ member)
    (List.sublist_append_left (importedConstraints trace.rom) importedConstraintsTimestampLookups)
  change FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints trace.rom) at core
  have metadata : entry.data.mask < 262144 ∧ entry.data.rd = match input.rd with | .Regidx bits => bits := by
    rw [encoding] at fields
    rcases input with ⟨⟨op, left, right, immediate, pc⟩, ⟨rs1⟩, ⟨rs2⟩, ⟨rd⟩, imm, upper, state⟩
    change BitVec 5 at rs1 rs2 rd
    cases op <;> by_cases zero : rd = (0#5)
    all_goals simp [arithmeticInstruction, decoderFields, Trace.decoderFields, arithmeticFields,
      Trace.arithmeticFields, DecoderData.mapFamily, zero] at fields
    all_goals rw [← fields]
    all_goals simp [zero]
  have spec : stepSpec (retiredState before (Control.initialPC w).toBitVec) (Sail.execution input) input.rd
      ⟨Control.destination w, Control.finalPC w⟩ := by
    change stepSpec input.before (Sail.execution input) input.rd _ at result
    rw [atRow] at result
    exact result
  have standard := register_retirement (by omega) core fields query metadata.1 metadata.2
    trace.memoryEpoch history spec
  refine ⟨Sail.execution input, ?_, standard⟩
  rw [encoding]
  cases op : input.row.opcode <;> simp [arithmeticInstruction, instructionClause, Sail.execution, op]

end Airbender.UnifiedReduced.Proofs
