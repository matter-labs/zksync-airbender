import Slop.Sail.ResetState
import Tests.ShiftBinopTimestamp
import Slop.ShiftBinop.Decoder
import Human.Trace.Execution
import Slop.Sail.WordMemoryState

namespace Tests.ShiftBinopDecoder
open Airbender Arithmetic Trace Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

private noncomputable def before (pc bits : BitVec 32) : State := wordWriteState Airbender.Reference.RiscV.Sail.resetMachine pc.toNat bits

theorem airbender_before (pc bits : BitVec 32) : Airbender.Reference.RiscV.Sail.Configured (before pc bits) := by
  configured_fixture [before, Airbender.Reference.RiscV.Sail.wordWriteState]

private def samples : List (BitVec 32 × SailRV32.instruction × DecoderData Unit) := [
  (0x0020c1b3, .RTYPE (.Regidx 2, .Regidx 1, .Regidx 3, .XOR), ⟨(), 1, 2, 3, ⟨0, 0⟩, 2, 4⟩),
  (0x0020e1b3, .RTYPE (.Regidx 2, .Regidx 1, .Regidx 3, .OR), ⟨(), 1, 2, 3, ⟨0, 0⟩, 2, 6⟩),
  (0x0020f1b3, .RTYPE (.Regidx 2, .Regidx 1, .Regidx 3, .AND), ⟨(), 1, 2, 3, ⟨0, 0⟩, 2, 7⟩),
  (0x002091b3, .RTYPE (.Regidx 2, .Regidx 1, .Regidx 3, .SLL), ⟨(), 1, 2, 3, ⟨0, 0⟩, 1, 1⟩),
  (0x0020d1b3, .RTYPE (.Regidx 2, .Regidx 1, .Regidx 3, .SRL), ⟨(), 1, 2, 3, ⟨0, 0⟩, 1, 2⟩),
  (0x4020d1b3, .RTYPE (.Regidx 2, .Regidx 1, .Regidx 3, .SRA), ⟨(), 1, 2, 3, ⟨0, 0⟩, 1, 3⟩),
  (0xfff0c193, .ITYPE (0xfff, .Regidx 1, .Regidx 3, .XORI), ⟨(), 1, 0, 3, ⟨255, 255⟩, 2, 4⟩),
  (0x1230e193, .ITYPE (0x123, .Regidx 1, .Regidx 3, .ORI), ⟨(), 1, 0, 3, ⟨35, 1⟩, 2, 6⟩),
  (0x0ff0f193, .ITYPE (0x0ff, .Regidx 1, .Regidx 3, .ANDI), ⟨(), 1, 0, 3, ⟨255, 0⟩, 2, 7⟩),
  (0x01f09193, .SHIFTIOP (31, .Regidx 1, .Regidx 3, .SLLI), ⟨(), 1, 0, 3, ⟨31, 0⟩, 1, 1⟩),
  (0x0000d193, .SHIFTIOP (0, .Regidx 1, .Regidx 3, .SRLI), ⟨(), 1, 0, 3, ⟨0, 0⟩, 1, 2⟩),
  (0x41f0d193, .SHIFTIOP (31, .Regidx 1, .Regidx 3, .SRAI), ⟨(), 1, 0, 3, ⟨31, 0⟩, 1, 3⟩)]

private theorem extraction (pc bits : BitVec 32) (instruction : SailRV32.instruction)
    (data : DecoderData Unit)
    (decoded : Airbender.Reference.RiscV.Sail.decodeOnReset bits = some instruction)
    (fields : Airbender.ShiftBinop.decoderFields instruction = some data) :
    Airbender.ShiftBinop.programImage (before pc bits) [pc] = some [⟨pc, bits, instruction, data⟩] := by
  have bytes : (Cell.ram pc).read (before pc bits) = .ok bits (before pc bits) :=
    by simpa only [Cell.read, before] using written_word_read Airbender.Reference.RiscV.Sail.resetMachine pc.toNat bits
  simp only [List.mapM_cons, List.mapM_nil, programEntryWith, bytes, decoded, fields,
    bind, Option.bind, pure]

/-- All twelve standard forms come from real public encodings, including
    negative binary immediates and the largest legal RV32 shift payload. -/
theorem all_instruction_forms : ∀ sample ∈ samples,
    Airbender.ShiftBinop.programImage (before 0 sample.1) [0] =
      some [⟨0, sample.1, sample.2.1, sample.2.2⟩] := by
  intro sample member
  simp only [samples, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals apply extraction _ _ _ _ <;> first | decode_on_reset | with_unfolding_all rfl

/-- The shared trace dispatcher selects the original Sail execution clauses
    for the same twelve publicly decoded instruction forms. -/
theorem all_instruction_clauses  :
    ∀ sample ∈ samples, (Trace.instructionClause sample.2.1).isSome = true := by
  intro sample member
  simp only [samples, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals rfl

private def xorEntry : Airbender.ShiftBinop.ProgramEntry :=
  ⟨65532, 0x000040b3, .RTYPE (.Regidx 0, .Regidx 0, .Regidx 1, .XOR),
    ⟨(), 0, 0, 1, ⟨0, 0⟩, 2, 4⟩⟩

/-- Production membership binds the actual aliased XOR row, not an expected
    decoded opcode supplied as a theorem premise. -/
theorem accepted_row_fetched (rollover : Bool) :
    Airbender.ShiftBinop.Fetched (Tests.ShiftBinopTimestamp.assignment rollover)
      (before xorEntry.pc xorEntry.bits) := by
  apply Airbender.ShiftBinop.Proofs.fetched (by decide)
    (extraction xorEntry.pc xorEntry.bits xorEntry.instruction xorEntry.data (by decode_on_reset) (by rfl))
    (Verification.holds_of_sublist (Tests.ShiftBinopTimestamp.constraints rollover)
      (List.sublist_append_left _ _))
  cases rollover <;> change ∃ i, _
  all_goals exact ⟨⟨0, by decide⟩, by decide⟩

/-- Decoder tags are checked independently of selector bits. -/
theorem wrong_tag_rejected :
    ¬ (Airbender.ShiftBinop.decoderTable [xorEntry]).Contains #[]
      (Airbender.ShiftBinop.decoderQuery
        (fun i => if i = 10 then 6 else Tests.ShiftBinopTimestamp.assignment false i)) := by
  intro member
  obtain ⟨entry, present, _, query⟩ := Proofs.decoder_member member
  simp only [List.mem_singleton] at present
  subst entry
  have tag := congrArg (fun q : Vector (ZMod babyBearModulus) 9 => q[7]) query
  exact (by decide :
    (Airbender.ShiftBinop.decoderQuery
      (fun i => if i = 10 then 6 else Tests.ShiftBinopTimestamp.assignment false i))[7] ≠
      (xorEntry.query : Vector (ZMod babyBearModulus) 9)[7]) tag

end Tests.ShiftBinopDecoder
