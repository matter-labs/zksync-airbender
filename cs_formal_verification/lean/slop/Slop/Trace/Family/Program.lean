import Slop.Trace.Family.Timestamps
import Slop.Trace.Program
import Slop.AddSub.Selectors
import Slop.WordMemory

namespace Airbender.Trace.Proofs
open Arithmetic

theorem query_pc {p : Nat} (hp : limbBase < p) {row : Row p} {entry : ProgramEntry}
    (equal : row.decoderQuery = entry.query) : row.start.word.toBitVec = entry.pc := by
  have word : row.start.word = Word.ofBitVec entry.pc := native_query_pc_word hp equal
  rw [word, Word.ofBitVec_roundtrip]

theorem query_immediate {p : Nat} (hp : limbBase < p) {row : Row p} {entry : ProgramEntry}
    (fields : decoderFields entry.instruction = some entry.data)
    (equal : row.decoderQuery = entry.query) : row.decoderImmediate.Bounded := by
  have bound := (decoder_field_bounds fields).1
  have word : row.decoderImmediate = entry.data.immediate := native_query_immediate_word hp bound equal
  exact word ▸ bound

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
    (decoded : Decoded trace program)
    (airbenderConfiguration : Reference.RiscV.Sail.Configured before := by find_configured) :
    ∀ row ∈ trace.rows, row.Fetched before projection := by
  intro row member
  obtain ⟨entry, present, family, equal⟩ := decoder_member (decoded row member)
  have source := program_sources image entry present
  exact ⟨entry, source, family, equal, query_pc hp equal,
    query_selectors_of_bound hp accepted member (maskBound _ _ source.fields) equal⟩

theorem decoder_soundness {p : Nat} [Fact p.Prime] (hp : limbBase < p)
    {trace : Data p} (accepted : Accepted trace) {before : Reference.RiscV.Sail.State}
    {addresses : List (BitVec 32)} {program : List ProgramEntry}
    (image : programImage before addresses = some program)
    (decoded : Decoded trace program)
    (airbenderConfiguration : Reference.RiscV.Sail.Configured before := by find_configured) :
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
  exact query_immediate hp (decoder_fields_of_image image entry present) equal

end Airbender.Trace.Proofs
