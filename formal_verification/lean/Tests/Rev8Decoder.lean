import Tests.SailDecoder
import Airbender.Proofs.ShiftBinop.Decoder
import Airbender.Proofs.Sail.WordMemoryState

namespace Tests.Rev8Decoder
open Airbender Arithmetic Trace Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

private def configured (enabled : Bool) : State :=
  { (default : State) with regs := ((default : State).regs.insert .misa
      (if enabled then (0x40000002 : BitVec 32) else 0x40000000)) }

private def before (enabled : Bool) : State :=
  wordWriteState (configured enabled) 0 0x6980d193

private def entry : Airbender.ShiftBinop.ProgramEntry :=
  ⟨0, 0x6980d193, .REV8 (.Regidx 1, .Regidx 3), ⟨(), 1, 0, 3, ⟨0, 0⟩, 1, 5⟩⟩

/-- Actual public bytes reach original REV8 decoding and native metadata.
    Both B configurations work: the pinned platform also supports Zbkb. -/
theorem actual_public_encoding (enabled : Bool) :
    Airbender.ShiftBinop.programImage (before enabled) [0] = some [entry] := by
  have bytes : (Cell.ram 0).read (before enabled) = .ok entry.bits (before enabled) :=
    written_word_read _ 0 _
  have isa : run (SailRV32.readReg .misa) (before enabled) =
      .ok (if enabled then (0x40000002 : BitVec 32) else 0x40000000) (before enabled) := by
    apply read_register
    simp [before, configured, wordWriteState]
  have decoded : run (SailRV32.Functions.encdec_backwards entry.bits) (before enabled) =
      .ok entry.instruction (before enabled) := by
    cases enabled
    all_goals
      repeat' first
        | (with_unfolding_all rfl)
        | (with_unfolding_all conv_lhs => arg 1; whnf
           rw [@run_read_cont (inferInstance : _root_.Sail.ArchSem.Arch)
             _ _ SailRV32.Register.misa _ _ _ isa])
  simp only [Airbender.ShiftBinop.programImage, List.mapM_cons, List.mapM_nil,
    programEntryRunWith, bytes, decoded, bind, Option.bind]
  rfl

end Tests.Rev8Decoder
