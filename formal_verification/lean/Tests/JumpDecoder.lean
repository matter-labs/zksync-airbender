import Airbender.Review.JumpBranchSlt.Theorems
import Airbender.Proofs.Sail.WordMemoryState
import Tests.JumpTimestamp

namespace Tests.JumpDecoder
open Airbender Arithmetic Trace
set_option warningAsError true
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

private def before (bits : BitVec 32) : Reference.RiscV.Sail.State :=
  Reference.RiscV.Sail.wordWriteState default 0 bits

private theorem extraction (bits : BitVec 32) (instruction : SailRV32.instruction)
    (data : DecoderData Unit)
    (decoded : SailRV32.Functions.encdec_backwards bits = .pure instruction)
    (fields : JumpBranchSlt.decoderFields instruction = some data) :
    JumpBranchSlt.programImage (before bits) [0] = some [⟨0, bits, instruction, data⟩] := by
  have bytes : (Cell.ram 0).read (before bits) = .ok bits (before bits) :=
    Reference.RiscV.Sail.written_word_read default 0 bits
  simp only [List.mapM_cons, List.mapM_nil, programEntryWith, bytes, decoded, fields,
    bind, Option.bind, pure]

private def samples : List (BitVec 32 × SailRV32.instruction × DecoderData Unit) := [
  (0x0020a1b3, .RTYPE (.Regidx 2, .Regidx 1, .Regidx 3, .SLT),
    ⟨(), 1, 2, 3, ⟨0, 0⟩, 4, 2⟩),
  (0x0020b1b3, .RTYPE (.Regidx 2, .Regidx 1, .Regidx 3, .SLTU),
    ⟨(), 1, 2, 3, ⟨0, 0⟩, 4, 3⟩),
  (0xfff0a193, .ITYPE (0xfff, .Regidx 1, .Regidx 3, .SLTI),
    ⟨(), 1, 0, 3, ⟨65535, 65535⟩, 4, 2⟩),
  (0xfff0b193, .ITYPE (0xfff, .Regidx 1, .Regidx 3, .SLTIU),
    ⟨(), 1, 0, 3, ⟨65535, 65535⟩, 4, 3⟩),
  (0x00208463, .BTYPE (8, .Regidx 2, .Regidx 1, .BEQ), ⟨(), 1, 2, 0, ⟨8, 0⟩, 24, 0⟩),
  (0x00209463, .BTYPE (8, .Regidx 2, .Regidx 1, .BNE), ⟨(), 1, 2, 0, ⟨8, 0⟩, 24, 1⟩),
  (0x0020c463, .BTYPE (8, .Regidx 2, .Regidx 1, .BLT), ⟨(), 1, 2, 0, ⟨8, 0⟩, 24, 4⟩),
  (0x0020d463, .BTYPE (8, .Regidx 2, .Regidx 1, .BGE), ⟨(), 1, 2, 0, ⟨8, 0⟩, 24, 5⟩),
  (0x0020e463, .BTYPE (8, .Regidx 2, .Regidx 1, .BLTU), ⟨(), 1, 2, 0, ⟨8, 0⟩, 24, 6⟩),
  (0x0020f463, .BTYPE (8, .Regidx 2, .Regidx 1, .BGEU), ⟨(), 1, 2, 0, ⟨8, 0⟩, 24, 7⟩),
  (0xffdff0ef, .JAL (0x1ffffc, .Regidx 1), ⟨(), 0, 0, 1, ⟨65532, 65535⟩, 1, 0⟩),
  (0xffdff06f, .JAL (0x1ffffc, .Regidx 0), ⟨(), 0, 0, 0, ⟨65532, 65535⟩, 17, 0⟩),
  (0xfff080e7, .JALR (0xfff, .Regidx 1, .Regidx 1), ⟨(), 1, 0, 1, ⟨65535, 65535⟩, 2, 0⟩),
  (0xfff08067, .JALR (0xfff, .Regidx 1, .Regidx 0), ⟨(), 1, 0, 0, ⟨65535, 65535⟩, 18, 0⟩)]

/-- All supported opcodes, negative immediates, aliased JALR and x0 jump writes
    are read from actual public bytes and decoded by the original Sail term. -/
theorem all_instruction_forms : ∀ sample ∈ samples,
    JumpBranchSlt.programImage (before sample.1) [0] =
      some [⟨0, sample.1, sample.2.1, sample.2.2⟩] := by
  intro sample member
  simp only [samples, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  all_goals exact extraction _ _ _ (by rfl) (by rfl)

/-- Native offset parity comes from the public-image constructor and original
    decoder, including all six branch forms and negative JAL offsets. -/
theorem actual_offset_parity : ∀ sample ∈ samples,
    match sample.2.1 with
    | .JAL _ | .BTYPE _ => sample.2.2.immediate.lo % 2 = 0
    | _ => True := by
  intro sample member
  have image := all_instruction_forms sample member
  have source := Proofs.program_sources image
    (⟨0, sample.1, sample.2.1, sample.2.2⟩ : JumpBranchSlt.ProgramEntry) (by simp)
  exact JumpBranchSlt.Proofs.decoder_offset_even source

/-- Discarded comparisons belong to ADD/SUB preprocessing, so this table
    cannot silently use a comparison row for them. -/
theorem discarded_comparisons_rejected :
    JumpBranchSlt.programImage (before 0x0020a033) [0] = none ∧
      JumpBranchSlt.programImage (before 0xfff0b013) [0] = none := by
  have bytes (bits : BitVec 32) : (Cell.ram 0).read (before bits) = .ok bits (before bits) :=
    Reference.RiscV.Sail.written_word_read default 0 bits
  constructor <;> simp only [List.mapM_cons, programEntryWith, bytes, bind, Option.bind] <;> rfl

private def entry : JumpBranchSlt.ProgramEntry :=
  ⟨0, 0xffdff0ef, .JAL (0x1ffffc, .Regidx 1), ⟨(), 0, 0, 1, ⟨65532, 65535⟩, 1, 0⟩⟩
private def assignment : Nat → ZMod babyBearModulus
  | 7 | 11 => 1 | 8 => 65532 | 9 => 65535 | _ => 0

theorem native_query : JumpBranchSlt.decoderQuery assignment = entry.query := by decide

theorem wrong_selector_rejected :
    ¬ (JumpBranchSlt.decoderTable [entry]).Contains #[]
      (JumpBranchSlt.decoderQuery (fun i => if i = 12 then 1 else assignment i)) := by
  intro member
  obtain ⟨actual, present, _, query⟩ := Proofs.decoder_member member
  simp only [List.mem_singleton] at present
  subst actual
  have mask := congrArg (fun q : Vector (ZMod babyBearModulus) 9 => q[8]) query
  exact (by decide :
    (JumpBranchSlt.decoderQuery (fun i => if i = 12 then 1 else assignment i))[8] ≠
      (entry.query : Vector (ZMod babyBearModulus) 9)[8]) mask

/-- The condition tag is bound even for JAL, where its correct value is zero. -/
theorem wrong_funct3_rejected :
    ¬ (JumpBranchSlt.decoderTable [entry]).Contains #[]
      (JumpBranchSlt.decoderQuery (fun i => if i = 10 then 1 else assignment i)) := by
  intro member
  obtain ⟨actual, present, _, query⟩ := Proofs.decoder_member member
  simp only [List.mem_singleton] at present
  subst actual
  have tag := congrArg (fun q : Vector (ZMod babyBearModulus) 9 => q[7]) query
  exact (by decide :
    (JumpBranchSlt.decoderQuery (fun i => if i = 10 then 1 else assignment i))[7] ≠
      (entry.query : Vector (ZMod babyBearModulus) 9)[7]) tag

/-- Every selector is recovered using the generic packing theorem, rather than
    adding the intended opcode as a premise. -/
theorem selector_recovery : ∀ i : Fin 5,
    assignment JumpBranchSlt.importedConstraintsDecoderColumns.flags[i] =
      if entry.data.mask.testBit i.val then 1 else 0 := by
  apply Proofs.unpack_decoder_bits_of_width (by decide) (by decide) (by decide)
  · intro i
    fin_cases i <;> decide
  · decide

/-- Apply the published fetch theorem to a complete accepted native JAL row,
    rather than a query-only fixture. -/
theorem accepted_row_fetched :
    JumpBranchSlt.Fetched (Tests.JumpTimestamp.assignment false) (before entry.bits) := by
  apply JumpBranchSlt.fetched (by decide)
    (extraction entry.bits entry.instruction entry.data (by rfl) (by rfl))
    (Verification.holds_of_sublist (Tests.JumpTimestamp.constraints false)
      (List.sublist_append_left _ _))
  change ∃ i, _
  exact ⟨⟨0, by decide⟩, by decide⟩

end Tests.JumpDecoder
