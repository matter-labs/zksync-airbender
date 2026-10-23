import Tests.SailDecoder
import Slop.ShiftBinop.Decoder
import Human.Trace.Execution
import Slop.Sail.WordMemoryState
import Slop.Sail.CheckedMemory

namespace Tests.Rev8Decoder
open Airbender Arithmetic Trace Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

private def before (state : State) : State :=
  wordWriteState state 0 0x6980d193

private def entry : Airbender.ShiftBinop.ProgramEntry :=
  ⟨0, 0x6980d193, .REV8 (.Regidx 1, .Regidx 3), ⟨(), 1, 0, 3, ⟨0, 0⟩, 1, 5⟩⟩

/-- Actual public bytes reach original REV8 decoding and native metadata on every Airbender state:
    misa (RV32 I + M) does not enable B, but the pinned platform supports Zbkb. -/
theorem actual_public_encoding {state : State} (configured : Configured state) :
    Airbender.ShiftBinop.programImage (before state) [0] = some [entry] := by
  have bytes : (Cell.ram 0).read (before state) = .ok entry.bits (before state) :=
    written_word_read _ 0 _
  have decoded : run (SailRV32.Functions.encdec_backwards entry.bits) (before state) =
      .ok entry.instruction (before state) :=
    Tests.SailDecoder.rev8 (configuration_word_write configured 0 _)
  simp only [Airbender.ShiftBinop.programImage, List.mapM_cons, List.mapM_nil,
    programEntryWith, bytes, decoded, bind, Option.bind]
  rfl

theorem actual_clause  :
    Trace.instructionClause entry.instruction =
      some (SailRV32.Functions.execute_REV8 (.Regidx 1) (.Regidx 3)) := rfl

end Tests.Rev8Decoder
