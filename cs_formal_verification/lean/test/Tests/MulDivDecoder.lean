import Slop.Sail.ResetState
import Tests.MulDivTimestamp
import Slop.Sail.WordMemoryState

namespace Tests.MulDivDecoder
open Airbender Arithmetic Trace
set_option warningAsError true
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

private def configured : Reference.RiscV.Sail.State :=
  { (default : Reference.RiscV.Sail.State) with
    regs := (default : Reference.RiscV.Sail.State).regs.insert .misa (0x40001000 : BitVec 32) }

private def before (pc bits : BitVec 32) : Reference.RiscV.Sail.State :=
  Reference.RiscV.Sail.wordWriteState configured pc.toNat bits

private theorem misa_read (pc bits : BitVec 32) :
    Reference.Sail.run (SailRV32.readReg .misa) (before pc bits) =
      .ok (0x40001000 : BitVec 32) (before pc bits) := by
  apply Reference.RiscV.Sail.read_register
  simp [before, configured, Reference.RiscV.Sail.wordWriteState]

private theorem extraction (pc bits : BitVec 32) (instruction : SailRV32.instruction)
    (data : DecoderData Unit)
    (decoded : Airbender.Reference.RiscV.Sail.decodeOnReset bits = some instruction)
    (fields : Airbender.MulDiv.decoderFields instruction = some data) :
    Airbender.MulDiv.programImage (before pc bits) [pc] = some [⟨pc, bits, instruction, data⟩] := by
  have bytes : (Cell.ram pc).read (before pc bits) = .ok bits (before pc bits) :=
    by simpa only [Cell.read, before] using
      Reference.RiscV.Sail.written_word_read configured pc.toNat bits
  simp only [List.mapM_cons, List.mapM_nil, programEntryWith, bytes, decoded, fields,
    bind, Option.bind, pure]

private def samples : List (BitVec 32 × SailRV32.instruction × DecoderData Unit) := [
  (0x022081b3, .MUL (.Regidx 2, .Regidx 1, .Regidx 3, ⟨.Low, .Signed, .Signed⟩),
    ⟨(), 1, 2, 3, ⟨0, 0⟩, 1, 0⟩),
  (0x0220b1b3, .MUL (.Regidx 2, .Regidx 1, .Regidx 3, ⟨.High, .Unsigned, .Unsigned⟩),
    ⟨(), 1, 2, 3, ⟨0, 0⟩, 2, 0⟩),
  (0x0220d1b3, .DIV (.Regidx 2, .Regidx 1, .Regidx 3, true),
    ⟨(), 1, 2, 3, ⟨0, 0⟩, 4, 0⟩),
  (0x0220f1b3, .REM (.Regidx 2, .Regidx 1, .Regidx 3, true),
    ⟨(), 1, 2, 3, ⟨0, 0⟩, 8, 0⟩)]

/-- Each of the four native forms is read from public bytes and decoded by
    the original Sail term, rather than supplied as a decoded instruction. -/
theorem all_instruction_forms : ∀ sample ∈ samples,
    Airbender.MulDiv.programImage (before 0 sample.1) [0] =
      some [⟨0, sample.1, sample.2.1, sample.2.2⟩] := by
  intro sample member
  simp only [samples, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  all_goals apply extraction _ _ _ _ (fields := by rfl)
  all_goals decode_on_reset

private def excluded : List (BitVec 32 × SailRV32.instruction) := [
  (0x022090b3, .MUL (.Regidx 2, .Regidx 1, .Regidx 1, ⟨.High, .Signed, .Signed⟩)),
  (0x0220a0b3, .MUL (.Regidx 2, .Regidx 1, .Regidx 1, ⟨.High, .Signed, .Unsigned⟩)),
  (0x0220c0b3, .DIV (.Regidx 2, .Regidx 1, .Regidx 1, false)),
  (0x0220e0b3, .REM (.Regidx 2, .Regidx 1, .Regidx 1, false)),
  (0x02208033, .MUL (.Regidx 2, .Regidx 1, .Regidx 0, ⟨.Low, .Signed, .Signed⟩)),
  (0x0220b033, .MUL (.Regidx 2, .Regidx 1, .Regidx 0, ⟨.High, .Unsigned, .Unsigned⟩)),
  (0x0220d033, .DIV (.Regidx 2, .Regidx 1, .Regidx 0, true)),
  (0x0220f033, .REM (.Regidx 2, .Regidx 1, .Regidx 0, true))]

private theorem extraction_rejected (bits : BitVec 32) (instruction : SailRV32.instruction)
    (decoded : Airbender.Reference.RiscV.Sail.decodeOnReset bits = some instruction)
    (fields : Airbender.MulDiv.decoderFields instruction = none) :
    Airbender.MulDiv.programImage (before 0 bits) [0] = none := by
  have bytes : (Cell.ram 0).read (before 0 bits) = .ok bits (before 0 bits) :=
    Reference.RiscV.Sail.written_word_read configured 0 bits
  simp only [List.mapM_cons, programEntryWith, bytes, decoded, fields, bind, Option.bind]

/-- Actual decoding rejects signed-family and discarded-destination forms. -/
theorem unsupported_forms_rejected : ∀ sample ∈ excluded,
    Airbender.MulDiv.programImage (before 0 sample.1) [0] = none := by
  intro sample member
  simp only [excluded, List.mem_cons, List.not_mem_nil, or_false] at member
  have fields : Airbender.MulDiv.decoderFields sample.2 = none := by
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  apply extraction_rejected sample.1 sample.2 ?_ fields
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decode_on_reset

private def entry (remainder : Bool) : Airbender.MulDiv.ProgramEntry :=
  ⟨0x3fffc, if remainder then 0x0220f0b3 else 0x0220d0b3,
    if remainder then .REM (.Regidx 2, .Regidx 1, .Regidx 1, true)
    else .DIV (.Regidx 2, .Regidx 1, .Regidx 1, true),
    ⟨(), 1, 2, 1, ⟨0, 0⟩, if remainder then 8 else 4, 0⟩⟩

/-- Apply the production fetch theorem to accepted DIVU/REMU-by-zero rows
    with aliased rs1/rd, including low-clock rollover. -/
theorem accepted_row_fetched (remainder rollover : Bool) :
    Airbender.MulDiv.Fetched (Tests.MulDivTimestamp.assignment remainder rollover)
      (before (entry remainder).pc (entry remainder).bits) := by
  apply Airbender.MulDiv.fetched (by decide)
    (extraction (entry remainder).pc (entry remainder).bits (entry remainder).instruction
      (entry remainder).data (by cases remainder <;> decode_on_reset) (by cases remainder <;> rfl))
    (Verification.holds_of_sublist (Tests.MulDivTimestamp.constraints remainder rollover)
      (List.sublist_append_left _ _))
  change ∃ i, _
  cases remainder <;> cases rollover <;> exact ⟨⟨0, by decide⟩, by decide⟩

/-- Changing a selector changes the packed query and is rejected by the
    table built from the actual public DIVU instruction. -/
theorem wrong_selector_rejected :
    ¬ (Airbender.MulDiv.decoderTable [entry false]).Contains #[]
      (Airbender.MulDiv.decoderQuery
        (fun i => if i = 10 then 1 else Tests.MulDivTimestamp.assignment false false i)) := by
  intro member
  obtain ⟨actual, present, _, query⟩ := Proofs.decoder_member member
  simp only [List.mem_singleton] at present
  subst actual
  have mask := congrArg (fun q : Vector (ZMod babyBearModulus) 9 => q[8]) query
  exact (by decide :
    (Airbender.MulDiv.decoderQuery
      (fun i => if i = 10 then 1 else Tests.MulDivTimestamp.assignment false false i))[8] ≠
      ((entry false).query : Vector (ZMod babyBearModulus) 9)[8]) mask

/-- The program image decodes on the Airbender configuration (`decodeOnReset`), so a state whose `misa`
    disables M still yields the multiplication row: the configuration is not read from the state. -/
theorem state_misa_ignored :
    let state := Reference.RiscV.Sail.wordWriteState
      { configured with regs := configured.regs.insert .misa (0x40000000 : BitVec 32) }
      0 (0x022081b3 : BitVec 32)
    Airbender.MulDiv.programImage state [0] =
      some [⟨0, 0x022081b3, .MUL (.Regidx 2, .Regidx 1, .Regidx 3, ⟨.Low, .Signed, .Signed⟩),
        ⟨(), 1, 2, 3, ⟨0, 0⟩, 1, 0⟩⟩] := by
  intro state
  have decoded : Airbender.Reference.RiscV.Sail.decodeOnReset 0x022081b3 =
      some (.MUL (.Regidx 2, .Regidx 1, .Regidx 3, ⟨.Low, .Signed, .Signed⟩)) := by decode_on_reset
  have bytes : (Cell.ram 0).read state = .ok 0x022081b3 state :=
    Reference.RiscV.Sail.written_word_read _ 0 _
  simp only [List.mapM_cons, List.mapM_nil, programEntryWith, bytes, decoded, bind, Option.bind, pure]
  rfl

end Tests.MulDivDecoder
