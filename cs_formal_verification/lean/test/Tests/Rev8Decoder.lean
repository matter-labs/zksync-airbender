import Slop.Sail.ResetState
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

/-- Original REV8 decoding on the Airbender configuration: misa (RV32 I + M) does not enable B, but the
    pinned platform supports Zbkb. -/
theorem decoded_on_reset : Airbender.Reference.RiscV.Sail.decodeOnReset entry.bits = some entry.instruction := by
  decode_on_reset

/-- The pinned Sail decoder returns REV8 on every Airbender state holding the public bytes. -/
theorem actual_decoding {state : State} (configured : Configured state) :
    run (SailRV32.Functions.encdec_backwards entry.bits) (before state) = .ok entry.instruction (before state) :=
  decode_on_reset_run (configured.with_mem _) decoded_on_reset

/-- Actual public bytes reach original REV8 decoding and native metadata on every state. -/
theorem actual_public_encoding {state : State} :
    Airbender.ShiftBinop.programImage (before state) [0] = some [entry] := by
  have bytes : (Cell.ram 0).read (before state) = .ok entry.bits (before state) :=
    written_word_read _ 0 _
  simp only [Airbender.ShiftBinop.programImage, List.mapM_cons, List.mapM_nil,
    programEntryWith, bytes, decoded_on_reset, bind, Option.bind]
  rfl

theorem actual_clause  :
    Trace.instructionClause entry.instruction =
      some (SailRV32.Functions.execute_REV8 (.Regidx 1) (.Regidx 3)) := rfl

end Tests.Rev8Decoder
