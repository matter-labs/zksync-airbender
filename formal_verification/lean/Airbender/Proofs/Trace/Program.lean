import Airbender.Review.Trace.Program
import Airbender.Proofs.Trace.InitialImage
import Airbender.Proofs.Trace.DecoderBits
import Airbender.Proofs.AddSub.Selectors
import Airbender.Proofs.WordMemory

namespace Airbender.Trace.Proofs
open Arithmetic

private theorem arithmetic_field_bounds (rs1 rs2 rd : BitVec 5) (bits : BitVec 32)
    {mask : Nat} (small : mask ≤ 4) :
    (arithmeticFields rs1 rs2 rd bits mask).immediate.Bounded ∧
      (arithmeticFields rs1 rs2 rd bits mask).mask ≤ 4 := by
  unfold arithmeticFields
  split
  · exact ⟨by simp [Word.Bounded, limbBase], by decide⟩
  · exact ⟨Word.ofBitVec_bound bits, small⟩

theorem decoder_field_bounds {instruction : SailRV32.instruction} {data : DecoderData}
    (fields : decoderFields instruction = some data) : data.immediate.Bounded ∧ data.mask ≤ 4 := by
  unfold decoderFields at fields
  split at fields
  case h_6 =>
    rename_i original imm rs1 rd
    change (if (rd : BitVec 5) = 0 then some (arithmeticFields 0 0 0 0 1)
      else some ⟨.wordMemory, rs1, 0, rd,
        Word.ofBitVec (SailRV32.Functions.sign_extend (m := 32) imm), 0⟩) = some data at fields
    by_cases zero : (rd : BitVec 5) = 0
    · rw [if_pos zero, Option.some.injEq] at fields
      subst data
      exact arithmetic_field_bounds _ _ _ _ (by decide)
    · rw [if_neg zero, Option.some.injEq] at fields
      subst data
      exact ⟨Word.ofBitVec_bound _, by change 0 ≤ 4; decide⟩
  all_goals first
    | (simp only [Option.some.injEq] at fields
       subst data
       exact arithmetic_field_bounds _ _ _ _ (by decide))
    | (simp only [Option.some.injEq] at fields
       subst data
       exact ⟨Word.ofBitVec_bound _, by dsimp; omega⟩)
    | (cases fields)

theorem entry_source {before : Reference.RiscV.Sail.State} {pc : BitVec 32}
    {entry : ProgramEntry} (image : programEntry before pc = some entry) :
    entry.pc = pc ∧ entry.Source before := by
  unfold programEntry at image
  cases read : (Cell.ram pc).read before with
  | error error after => simp [read, bind, Option.bind] at image
  | ok bits after =>
    have frame := cell_read_frame (.ram pc) read
    subst after
    simp only [read, bind, Option.bind] at image
    cases decoded : SailRV32.Functions.encdec_backwards bits with
    | impure _ _ => simp [decoded] at image
    | pure instruction =>
      simp only [decoded] at image
      cases fields : decoderFields instruction with
      | none => simp [fields] at image
      | some data =>
        simp only [fields, pure, Option.some.injEq] at image
        subst entry
        exact ⟨rfl, ⟨read, fun state => by rw [decoded]; rfl, fields⟩⟩

theorem program_sources {before : Reference.RiscV.Sail.State}
    {addresses : List (BitVec 32)} {program : List ProgramEntry}
    (image : programImage before addresses = some program) :
    ∀ entry ∈ program, entry.Source before := by
  unfold programImage at image
  induction addresses generalizing program with
  | nil =>
    simp only [List.mapM_nil, pure, Option.some.injEq] at image
    subst program
    simp
  | cons address addresses ih =>
    rw [List.mapM_cons] at image
    cases first : programEntry before address with
    | none => simp [first, bind, Option.bind] at image
    | some entry =>
      cases rest : addresses.mapM (programEntry before) with
      | none => simp [first, rest, bind, Option.bind] at image
      | some entries =>
        simp only [first, rest, bind, Option.bind, pure,
          Option.some.injEq] at image
        subst program
        intro actual member
        rcases List.mem_cons.mp member with rfl | member
        · exact (entry_source first).2
        · exact ih rest actual member

theorem decoder_member {p : Nat} [Fact p.Prime] {program : List ProgramEntry}
    {family : Family} {query : Vector (ZMod p) 9}
    (member : (decoderTable program family).Contains #[] query) :
    ∃ entry ∈ program, entry.data.family = family ∧ query = entry.query := by
  change ∃ i, query = ((program.filter fun entry => entry.data.family == family).get i).query at member
  obtain ⟨i, equal⟩ := member
  have present := List.get_mem (program.filter fun entry => entry.data.family == family) i
  obtain ⟨present, selected⟩ := List.mem_filter.mp present
  exact ⟨_, present, by simpa using selected, equal⟩

theorem query_pc {p : Nat} (hp : limbBase < p) {row : Row p} {entry : ProgramEntry}
    (equal : row.decoderQuery = entry.query) : row.start.word.toBitVec = entry.pc := by
  have low := congrArg (fun q : Vector (ZMod p) 9 => q[0]) equal
  have high := congrArg (fun q : Vector (ZMod p) 9 => q[1]) equal
  change row.start.pc.1 = ((Word.ofBitVec entry.pc).lo : ZMod p) at low
  change row.start.pc.2 = ((Word.ofBitVec entry.pc).hi : ZMod p) at high
  have bound := Word.ofBitVec_bound entry.pc
  have lo : (Word.ofBitVec entry.pc).lo < p := lt_trans bound.1 hp
  have hi : (Word.ofBitVec entry.pc).hi < p := lt_trans bound.2 hp
  have word : row.start.word = Word.ofBitVec entry.pc := by
    unfold PCState.State.word
    rw [low, high, ZMod.val_natCast_of_lt lo, ZMod.val_natCast_of_lt hi]
  rw [word, Word.ofBitVec_roundtrip]

theorem query_immediate {p : Nat} (hp : limbBase < p) {row : Row p} {entry : ProgramEntry}
    (fields : decoderFields entry.instruction = some entry.data)
    (equal : row.decoderQuery = entry.query) : row.decoderImmediate.Bounded := by
  have low := congrArg (fun q : Vector (ZMod p) 9 => q[5]) equal
  have high := congrArg (fun q : Vector (ZMod p) 9 => q[6]) equal
  change row.assignment row.decoderColumns.immediate[0] = (entry.data.immediate.lo : ZMod p) at low
  change row.assignment row.decoderColumns.immediate[1] = (entry.data.immediate.hi : ZMod p) at high
  have bound := (decoder_field_bounds fields).1
  unfold Row.decoderImmediate Word.Bounded
  rw [low, high, ZMod.val_natCast_of_lt (lt_trans bound.1 hp),
    ZMod.val_natCast_of_lt (lt_trans bound.2 hp)]
  exact bound

theorem query_selectors {p : Nat} [Fact p.Prime] (hp : limbBase < p)
    {trace : Data p} (accepted : Accepted trace) {row : Row p} (member : row ∈ trace.rows)
    {entry : ProgramEntry} (fields : decoderFields entry.instruction = some entry.data)
    (equal : row.decoderQuery = entry.query) :
    ∀ i : Fin row.decoderColumns.flags.size,
      row.assignment row.decoderColumns.flags[i] = if entry.data.mask.testBit i.val then 1 else 0 := by
  have small := (decoder_field_bounds fields).2
  have constraints := accepted.constraints row member
  have packed := congrArg (fun q : Vector (ZMod p) 9 => q[8]) equal
  cases row with
  | mk family w =>
    cases family with
    | addSub =>
      have core := Verification.holds_of_sublist constraints
        (List.sublist_append_left AddSub.importedConstraints AddSub.importedConstraintsTimestampLookups)
      have flags := (AddSub.Proofs.local_flags core).2
      have boolean : ∀ i : Fin 9, w #[10, 11, 12, 13, 14, 15, 16, 17, 18][i] = 0 ∨
          w #[10, 11, 12, 13, 14, 15, 16, 17, 18][i] = 1 := by
        intro i
        have bit := flags i
        fin_cases i <;> simpa using bit
      change (∑ i : Fin 9, (2 ^ i.val : Nat) * w #[10, 11, 12, 13, 14, 15, 16, 17, 18][i]) =
        (entry.data.mask : ZMod p) at packed
      exact unpack_decoder_bits (by dsimp [limbBase] at hp; omega) small boolean packed
    | wordMemory =>
      have core := Verification.holds_of_sublist constraints
        (List.sublist_append_left (WordMemory.importedConstraints trace.rom)
          WordMemory.importedConstraintsTimestampLookups)
      have boolean : w 10 = 0 ∨ w 10 = 1 := WordMemory.Proofs.local_flags core 1
      change (∑ i : Fin 1, (2 ^ i.val : Nat) * w #[10][i]) = (entry.data.mask : ZMod p) at packed
      have scalar : w 10 = (entry.data.mask : ZMod p) := by simpa using packed
      have value := congrArg ZMod.val scalar
      rw [ZMod.val_natCast_of_lt (by dsimp [limbBase] at hp; omega : entry.data.mask < p)] at value
      change ∀ i : Fin 1, w #[10][i] = if entry.data.mask.testBit i.val then 1 else 0
      intro i
      have index : i = 0 := Fin.eq_zero i
      subst i
      rcases boolean with zero | one
      · simp only [zero, ZMod.val_zero] at value
        rw [← value]
        exact zero
      · have oneval : (1 : ZMod p).val = 1 := by
          simpa only [Nat.cast_one] using (ZMod.val_natCast_of_lt (by dsimp [limbBase] at hp; omega : 1 < p))
        simp only [one, oneval] at value
        rw [← value]
        exact one

theorem decoder_soundness {p : Nat} [Fact p.Prime] (hp : limbBase < p)
    {trace : Data p} (accepted : Accepted trace) {before : Reference.RiscV.Sail.State}
    {addresses : List (BitVec 32)} {program : List ProgramEntry}
    (image : programImage before addresses = some program) (decoded : Decoded trace program) :
    ∀ row ∈ trace.rows, row.Fetched before := by
  intro row member
  obtain ⟨entry, present, family, equal⟩ := decoder_member (decoded row member)
  have source := program_sources image entry present
  exact ⟨entry, source, family, equal, query_pc hp equal,
    query_selectors hp accepted member source.fields equal⟩

theorem decoder_immediate_bounds {p : Nat} [Fact p.Prime] (hp : limbBase < p)
    {trace : Data p} {before : Reference.RiscV.Sail.State}
    {addresses : List (BitVec 32)} {program : List ProgramEntry}
    (image : programImage before addresses = some program) (decoded : Decoded trace program) :
    ∀ row ∈ trace.rows, row.decoderImmediate.Bounded := by
  intro row member
  obtain ⟨entry, present, _, equal⟩ := decoder_member (decoded row member)
  exact query_immediate hp (program_sources image entry present).fields equal

end Airbender.Trace.Proofs
