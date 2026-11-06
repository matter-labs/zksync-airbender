import Slop.Sail.ResetState
import Tests.SubwordMemoryTimestamp
import Slop.SubwordMemory.Decoder
import Human.Trace.Execution
import Slop.Sail.WordMemoryState

namespace Tests.SubwordMemoryDecoder
open Airbender Arithmetic Trace Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

private noncomputable def before (pc bits : BitVec 32) : State := wordWriteState Airbender.Reference.RiscV.Sail.resetMachine pc.toNat bits

theorem airbender_before (pc bits : BitVec 32) : Airbender.Reference.RiscV.Sail.Configured (before pc bits) := by
  configured_fixture [before, Airbender.Reference.RiscV.Sail.wordWriteState]

private def samples : List (BitVec 32 × SailRV32.instruction × DecoderData Unit) := [
  (0xfff08183, .LOAD (4095, .Regidx 1, .Regidx 3, false, 1), ⟨(), 1, 0, 3, ⟨65535, 65535⟩, 6, 0⟩),
  (0x0010c183, .LOAD (1, .Regidx 1, .Regidx 3, true, 1), ⟨(), 1, 0, 3, ⟨1, 0⟩, 2, 0⟩),
  (0x00209183, .LOAD (2, .Regidx 1, .Regidx 3, false, 2), ⟨(), 1, 0, 3, ⟨2, 0⟩, 4, 0⟩),
  (0x0000d183, .LOAD (0, .Regidx 1, .Regidx 3, true, 2), ⟨(), 1, 0, 3, ⟨0, 0⟩, 0, 0⟩),
  (0xfe208fa3, .STORE (4095, .Regidx 2, .Regidx 1, 1), ⟨(), 1, 2, 0, ⟨65535, 65535⟩, 3, 0⟩),
  (0x00209123, .STORE (2, .Regidx 2, .Regidx 1, 2), ⟨(), 1, 2, 0, ⟨2, 0⟩, 1, 0⟩)]

private theorem extraction (pc bits : BitVec 32) (instruction : SailRV32.instruction)
    (data : DecoderData Unit)
    (decoded : Airbender.Reference.RiscV.Sail.decodeOnReset bits = some instruction)
    (fields : Airbender.SubwordMemory.decoderFields instruction = some data) :
    Airbender.SubwordMemory.programImage (before pc bits) [pc] = some [⟨pc, bits, instruction, data⟩] := by
  have bytes : (Cell.ram pc).read (before pc bits) = .ok bits (before pc bits) :=
    by simpa only [Cell.read, before] using written_word_read Airbender.Reference.RiscV.Sail.resetMachine pc.toNat bits
  simp only [List.mapM_cons, List.mapM_nil, programEntryWith, bytes, decoded, fields,
    bind, Option.bind, pure]

/-- All six byte/halfword forms come from original Sail decoding of actual
    public encodings, including negative load/store immediates. -/
theorem all_instruction_forms : ∀ sample ∈ samples,
    Airbender.SubwordMemory.programImage (before 0 sample.1) [0] =
      some [⟨0, sample.1, sample.2.1, sample.2.2⟩] := by
  intro sample member
  simp only [samples, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals apply extraction _ _ _ _ <;> first | decode_on_reset | with_unfolding_all rfl

theorem all_instruction_clauses  :
    ∀ sample ∈ samples, (Trace.instructionClause sample.2.1).isSome = true := by
  intro sample member
  simp only [samples, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals rfl

private def entry : Airbender.SubwordMemory.ProgramEntry :=
  ⟨0, 0x0000c103, .LOAD (0, .Regidx 1, .Regidx 2, true, 1),
    ⟨(), 1, 0, 2, ⟨0, 0⟩, 2, 0⟩⟩

/-- Production membership fixes the complete accepted LBU row's decoder
    interface from public bytes, independent of its clock rollover. -/
theorem accepted_row_fetched (rollover : Bool) :
    Airbender.SubwordMemory.Fetched (Tests.SubwordMemoryTimestamp.assignment rollover)
      (before entry.pc entry.bits) := by
  apply Airbender.SubwordMemory.Proofs.fetched (by decide)
    (extraction entry.pc entry.bits entry.instruction entry.data (by decode_on_reset) (by rfl))
    (airbender_before _ _)
    (Verification.holds_of_sublist (Tests.SubwordMemoryTimestamp.constraints rollover)
      (List.sublist_append_left _ _))
  cases rollover <;> change ∃ i, _
  all_goals exact ⟨⟨0, by decide⟩, by decide⟩

theorem wrong_selector_rejected :
    ¬ (Airbender.SubwordMemory.decoderTable [entry]).Contains #[]
      (Airbender.SubwordMemory.decoderQuery
        (fun i => if i = 12 then 1 else Tests.SubwordMemoryTimestamp.assignment false i)) := by
  intro member
  obtain ⟨actual, present, _, query⟩ := Proofs.decoder_member member
  simp only [List.mem_singleton] at present
  subst actual
  have mask := congrArg (fun q : Vector (ZMod babyBearModulus) 9 => q[8]) query
  exact (by decide :
    (Airbender.SubwordMemory.decoderQuery
      (fun i => if i = 12 then 1 else Tests.SubwordMemoryTimestamp.assignment false i))[8] ≠
      (entry.query : Vector (ZMod babyBearModulus) 9)[8]) mask

/-- Discarded destinations and the word-memory family are not admitted by
    this native projection, even though they are valid Sail instructions. -/
theorem excluded_forms :
    Airbender.SubwordMemory.decoderFields (.LOAD (0, .Regidx 1, .Regidx 0, true, 1)) = none ∧
    Airbender.SubwordMemory.decoderFields (.LOAD (0, .Regidx 1, .Regidx 0, false, 2)) = none ∧
    Airbender.SubwordMemory.decoderFields (.LOAD (0, .Regidx 1, .Regidx 2, false, 4)) = none := by
  decide

end Tests.SubwordMemoryDecoder
