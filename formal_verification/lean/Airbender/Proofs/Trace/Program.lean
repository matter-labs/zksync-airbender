import Airbender.Review.Trace.Program
import Airbender.Proofs.Trace.InitialImage
import Airbender.Proofs.Trace.DecoderBits
import Airbender.Proofs.AddSub.Selectors
import Airbender.Proofs.WordMemory
import Airbender.Proofs.Sail.DecoderFrame

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
        Word.ofBitVec (SailRV32.Functions.sign_extend (m := 32) imm), 0, 0⟩) = some data at fields
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

theorem entry_source {Kind : Type} {before : Reference.RiscV.Sail.State} {pc : BitVec 32}
    {entry : ProgramEntry Kind}
    {projection : SailRV32.instruction → Option (DecoderData Kind)}
    (image : programEntryWith projection before pc = some entry) :
    entry.pc = pc ∧ entry.SourceWith before projection := by
  unfold programEntryWith at image
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
      cases fields : projection instruction with
      | none => simp [fields] at image
      | some data =>
        simp only [fields, pure, Option.some.injEq] at image
        subst entry
        exact ⟨rfl, ⟨read, by rw [decoded]; rfl, fields⟩⟩

theorem program_sources {Kind : Type} {before : Reference.RiscV.Sail.State}
    {addresses : List (BitVec 32)} {program : List (ProgramEntry Kind)}
    {projection : SailRV32.instruction → Option (DecoderData Kind)}
    (image : programImageWith projection before addresses = some program) :
    ∀ entry ∈ program, entry.SourceWith before projection := by
  unfold programImageWith at image
  induction addresses generalizing program with
  | nil =>
    simp only [List.mapM_nil, pure, Option.some.injEq] at image
    subst program
    simp
  | cons address addresses ih =>
    rw [List.mapM_cons] at image
    cases first : programEntryWith projection before address with
    | none => simp [first, bind, Option.bind] at image
    | some entry =>
      cases rest : addresses.mapM (programEntryWith projection before) with
      | none => simp [first, rest, bind, Option.bind] at image
      | some entries =>
        simp only [first, rest, bind, Option.bind, pure,
          Option.some.injEq] at image
        subst program
        intro actual member
        rcases List.mem_cons.mp member with rfl | member
        · exact (entry_source first).2
        · exact ih rest actual member

theorem run_entry_source {Kind : Type} {before : Reference.RiscV.Sail.State} {pc : BitVec 32}
    {entry : ProgramEntry Kind}
    {projection : SailRV32.instruction → Option (DecoderData Kind)}
    (image : programEntryRunWith projection before pc = some entry) :
    entry.pc = pc ∧ entry.SourceWith before projection := by
  unfold programEntryRunWith at image
  cases read : (Cell.ram pc).read before with
  | error error after => simp [read, bind, Option.bind] at image
  | ok bits after =>
    have frame := cell_read_frame (.ram pc) read
    subst after
    simp only [read, bind, Option.bind] at image
    cases decoded : Reference.Sail.run (SailRV32.Functions.encdec_backwards bits) before with
    | error error after => simp [decoded] at image
    | ok instruction after =>
      simp only [decoded] at image
      cases fields : projection instruction with
      | none => simp [fields] at image
      | some data =>
        simp only [fields, pure, Option.some.injEq] at image
        subst entry
        exact ⟨rfl, ⟨read, (Reference.Sail.decoded_misa_frame _ decoded).2 before rfl, fields⟩⟩

theorem run_program_sources {Kind : Type} {before : Reference.RiscV.Sail.State}
    {addresses : List (BitVec 32)} {program : List (ProgramEntry Kind)}
    {projection : SailRV32.instruction → Option (DecoderData Kind)}
    (image : programImageRunWith projection before addresses = some program) :
    ∀ entry ∈ program, entry.SourceWith before projection := by
  unfold programImageRunWith at image
  induction addresses generalizing program with
  | nil =>
    simp only [List.mapM_nil, pure, Option.some.injEq] at image
    subst program
    simp
  | cons address addresses ih =>
    rw [List.mapM_cons] at image
    cases first : programEntryRunWith projection before address with
    | none => simp [first, bind, Option.bind] at image
    | some entry =>
      cases rest : addresses.mapM (programEntryRunWith projection before) with
      | none => simp [first, rest, bind, Option.bind] at image
      | some entries =>
        simp only [first, rest, bind, Option.bind, pure, Option.some.injEq] at image
        subst program
        intro actual member
        rcases List.mem_cons.mp member with rfl | member
        · exact (run_entry_source first).2
        · exact ih rest actual member

theorem decoder_member {Kind : Type} [DecidableEq Kind]
    {p : Nat} [Fact p.Prime] {program : List (ProgramEntry Kind)}
    {family : Kind} {query : Vector (ZMod p) 9}
    (member : (decoderTable program family).Contains #[] query) :
    ∃ entry ∈ program, entry.data.family = family ∧ query = entry.query := by
  change ∃ i, query = ((program.filter fun entry => entry.data.family == family).get i).query at member
  obtain ⟨i, equal⟩ := member
  have present := List.get_mem (program.filter fun entry => entry.data.family == family) i
  obtain ⟨present, selected⟩ := List.mem_filter.mp present
  exact ⟨_, present, by simpa using selected, equal⟩

theorem word_of_pc_query {p : Nat} (hp : limbBase < p) {lo hi : ZMod p} {pc : BitVec 32}
    (low : lo = ((Word.ofBitVec pc).lo : ZMod p))
    (high : hi = ((Word.ofBitVec pc).hi : ZMod p)) :
    (⟨lo.val, hi.val⟩ : Word) = Word.ofBitVec pc := by
  have bound := Word.ofBitVec_bound pc
  rw [low, high, ZMod.val_natCast_of_lt (lt_trans bound.1 hp),
    ZMod.val_natCast_of_lt (lt_trans bound.2 hp)]

/-- The native fetch query fixes both canonical PC limbs, for any family. -/
theorem native_query_pc_word {Kind : Type} {p : Nat} (hp : limbBase < p)
    {columns : TraceColumns} {decoder : DecoderColumns} {w : Nat → ZMod p}
    {entry : ProgramEntry Kind}
    (equal : nativeDecoderQuery columns decoder w = entry.query) :
    (⟨(w columns.initialPC[0]).val, (w columns.initialPC[1]).val⟩ : Word) =
      Word.ofBitVec entry.pc := by
  have low := congrArg (fun q : Vector (ZMod p) 9 => q[0]) equal
  have high := congrArg (fun q : Vector (ZMod p) 9 => q[1]) equal
  change w columns.initialPC[0] = ((Word.ofBitVec entry.pc).lo : ZMod p) at low
  change w columns.initialPC[1] = ((Word.ofBitVec entry.pc).hi : ZMod p) at high
  exact word_of_pc_query hp low high

theorem query_pc {p : Nat} (hp : limbBase < p) {row : Row p} {entry : ProgramEntry}
    (equal : row.decoderQuery = entry.query) : row.start.word.toBitVec = entry.pc := by
  have word : row.start.word = Word.ofBitVec entry.pc := native_query_pc_word hp equal
  rw [word, Word.ofBitVec_roundtrip]

/-- The same imported query fixes immediate limbs for every circuit family. -/
theorem native_query_immediate_word {Kind : Type} {p : Nat} (hp : limbBase < p)
    {columns : TraceColumns} {decoder : DecoderColumns} {w : Nat → ZMod p}
    {entry : ProgramEntry Kind} (bound : entry.data.immediate.Bounded)
    (equal : nativeDecoderQuery columns decoder w = entry.query) :
    (⟨(w decoder.immediate[0]).val, (w decoder.immediate[1]).val⟩ : Word) =
      entry.data.immediate := by
  have low := congrArg (fun q : Vector (ZMod p) 9 => q[5]) equal
  have high := congrArg (fun q : Vector (ZMod p) 9 => q[6]) equal
  change w decoder.immediate[0] = (entry.data.immediate.lo : ZMod p) at low
  change w decoder.immediate[1] = (entry.data.immediate.hi : ZMod p) at high
  rw [low, high, ZMod.val_natCast_of_lt (lt_trans bound.1 hp),
    ZMod.val_natCast_of_lt (lt_trans bound.2 hp)]

theorem query_immediate {p : Nat} (hp : limbBase < p) {row : Row p} {entry : ProgramEntry}
    (fields : decoderFields entry.instruction = some entry.data)
    (equal : row.decoderQuery = entry.query) : row.decoderImmediate.Bounded := by
  have bound := (decoder_field_bounds fields).1
  have word : row.decoderImmediate = entry.data.immediate := native_query_immediate_word hp bound equal
  exact word ▸ bound

/-- Canonical register indices from any family's imported nine-column query. -/
theorem native_query_indices {Kind : Type} {p : Nat} (hp : limbBase < p)
    {columns : TraceColumns} {decoder : DecoderColumns} {w : Nat → ZMod p}
    {entry : ProgramEntry Kind}
    (equal : nativeDecoderQuery columns decoder w = entry.query) :
    (w decoder.rs1).val = entry.data.rs1.toNat ∧
    (w decoder.rs2).val = entry.data.rs2.toNat ∧
    (w decoder.rd).val = entry.data.rd.toNat := by
  have scalar {column : Nat} {index : BitVec 5}
      (same : w column = (index.toNat : ZMod p)) : (w column).val = index.toNat := by
    rw [same, ZMod.val_natCast_of_lt (lt_trans index.isLt (by dsimp [limbBase] at hp; omega))]
  exact ⟨scalar (congrArg (fun q : Vector (ZMod p) 9 => q[2]) equal),
    scalar (congrArg (fun q : Vector (ZMod p) 9 => q[3]) equal),
    scalar (congrArg (fun q : Vector (ZMod p) 9 => q[4]) equal)⟩

/-- All three native register indices are fixed by the same decoder query. -/
theorem query_register_indices {p : Nat} (hp : limbBase < p) {row : Row p} {entry : ProgramEntry}
    (equal : row.decoderQuery = entry.query) :
    (row.assignment row.decoderColumns.rs1).val = entry.data.rs1.toNat ∧
    (row.assignment row.decoderColumns.rs2).val = entry.data.rs2.toNat ∧
    (row.assignment row.decoderColumns.rd).val = entry.data.rd.toNat :=
  native_query_indices hp equal

theorem query_immediate_value {p : Nat} (hp : limbBase < p) {row : Row p} {entry : ProgramEntry}
    (fields : decoderFields entry.instruction = some entry.data)
    (equal : row.decoderQuery = entry.query) : row.decoderImmediate = entry.data.immediate :=
  native_query_immediate_word hp (decoder_field_bounds fields).1 equal

theorem row_query_selectors_of_bound {p : Nat} [Fact p.Prime] (hp : limbBase < p)
    {row : Row p} (setup : Table (ZMod p) (fields 9))
    (constraints : FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment)
      (row.constraints setup))
    {entry : ProgramEntry} (small : entry.data.mask < 512)
    (equal : row.decoderQuery = entry.query) :
    ∀ i : Fin row.decoderColumns.flags.size,
      row.assignment row.decoderColumns.flags[i] = if entry.data.mask.testBit i.val then 1 else 0 := by
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
        (List.sublist_append_left (WordMemory.importedConstraints setup)
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

theorem query_selectors_of_bound {p : Nat} [Fact p.Prime] (hp : limbBase < p)
    {trace : Data p} (accepted : Accepted trace) {row : Row p} (member : row ∈ trace.rows)
    {entry : ProgramEntry} (small : entry.data.mask < 512)
    (equal : row.decoderQuery = entry.query) :
    ∀ i : Fin row.decoderColumns.flags.size,
      row.assignment row.decoderColumns.flags[i] = if entry.data.mask.testBit i.val then 1 else 0 :=
  row_query_selectors_of_bound hp trace.rom (accepted.constraints row member) small equal

theorem query_selectors {p : Nat} [Fact p.Prime] (hp : limbBase < p)
    {trace : Data p} (accepted : Accepted trace) {row : Row p} (member : row ∈ trace.rows)
    {entry : ProgramEntry} (fields : decoderFields entry.instruction = some entry.data)
    (equal : row.decoderQuery = entry.query) :
    ∀ i : Fin row.decoderColumns.flags.size,
      row.assignment row.decoderColumns.flags[i] = if entry.data.mask.testBit i.val then 1 else 0 :=
  query_selectors_of_bound hp accepted member (by have bound := (decoder_field_bounds fields).2; omega) equal

/-- Fetch and the Sail decoder are shared; the chosen projection only controls
    native metadata. Boolean packing recovers every selector for any nine-bit mask. -/
theorem decoder_soundness_with {p : Nat} [Fact p.Prime] (hp : limbBase < p)
    {projection : SailRV32.instruction → Option DecoderData}
    (maskBound : ∀ instruction data, projection instruction = some data → data.mask < 512)
    {trace : Data p} (accepted : Accepted trace) {before : Reference.RiscV.Sail.State}
    {addresses : List (BitVec 32)} {program : List ProgramEntry}
    (image : programImageWith projection before addresses = some program)
    (decoded : Decoded trace program) :
    ∀ row ∈ trace.rows, row.Fetched before projection := by
  intro row member
  obtain ⟨entry, present, family, equal⟩ := decoder_member (decoded row member)
  have source := program_sources image entry present
  exact ⟨entry, source, family, equal, query_pc hp equal,
    query_selectors_of_bound hp accepted member (maskBound _ _ source.fields) equal⟩

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
