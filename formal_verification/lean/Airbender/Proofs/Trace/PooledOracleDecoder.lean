import Airbender.Review.Trace.PooledNonDeterminism
import Airbender.Proofs.Trace.NonDeterminism
import Airbender.Proofs.Trace.PooledProgram

namespace Airbender.Trace.NonDeterminism.Pooled.Proofs
open Arithmetic Trace.Proofs

theorem fields_cases {instruction : SailRV32.instruction} {data : DecoderData PooledFamily}
    (fields : Pooled.decoderFields instruction = some data) :
    (∃ d, NonDeterminism.decoderFields instruction = some d ∧
      data = d.mapFamily pooledArithmeticFamily) ∨
      pooledDecoderFields instruction = some data := by
  unfold Pooled.decoderFields at fields
  cases selected : NonDeterminism.decoderFields instruction with
  | none => exact Or.inr (by simpa [selected] using fields)
  | some original =>
    exact Or.inl ⟨original, rfl, (Option.some.inj (by simpa [selected] using fields)).symm⟩

theorem source_cases {before : Reference.RiscV.Sail.State} {entry : PooledProgramEntry}
    (source : entry.SourceWith before Pooled.decoderFields) :
    PooledSource before entry NonDeterminism.decoderFields := by
  rcases fields_cases source.fields with ⟨data, fields, equal⟩ | fields
  · exact Or.inl ⟨⟨entry.pc, entry.bits, entry.instruction, data⟩,
      ⟨source.bytes, source.decoded, fields⟩, by cases entry; simp_all [ProgramEntry.mapFamily]⟩
  · have original : entry.SourceWith before pooledDecoderFields :=
      ⟨source.bytes, source.decoded, fields⟩
    rcases pooled_source_cases original with base | branch | multiply | shift | memory
    · obtain ⟨originalEntry, originalSource, equal⟩ := base
      exact Or.inl ⟨originalEntry, ⟨originalSource.bytes, originalSource.decoded,
        NonDeterminism.Proofs.standard_fields originalSource.fields⟩, equal⟩
    · exact Or.inr (Or.inl branch)
    · exact Or.inr (Or.inr (Or.inl multiply))
    · exact Or.inr (Or.inr (Or.inr (Or.inl shift)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr memory)))

private theorem standard_not_read {instruction : SailRV32.instruction}
    {data : DecoderData PooledFamily} (fields : pooledDecoderFields instruction = some data) :
    NonDeterminism.instructionRead instruction = false := by
  unfold NonDeterminism.instructionRead
  split
  · simp [pooledDecoderFields, Trace.decoderFields, JumpBranchSlt.decoderFields,
      MulDiv.decoderFields, ShiftBinop.decoderFields, SubwordMemory.decoderFields] at fields
  · rfl

private theorem standard_mask {instruction : SailRV32.instruction}
    {data : DecoderData PooledFamily} (fields : pooledDecoderFields instruction = some data)
    (family : data.family = .addSub) : data.mask < 256 := by
  rcases pooled_fields_cases fields with h | h | h | h | h
  · obtain ⟨original, selected, rfl⟩ := h
    exact lt_of_le_of_lt (decoder_field_bounds selected).2 (by decide)
  all_goals obtain ⟨original, _, rfl⟩ := h
  all_goals cases family

private theorem restricted_read {instruction : SailRV32.instruction} {data : DecoderData}
    (fields : NonDeterminism.decoderFields instruction = some data) :
    data.mask.testBit 8 = NonDeterminism.instructionRead instruction := by
  rcases NonDeterminism.Proofs.fields_cases fields with standard | h | h
  · have bound := (decoder_field_bounds standard).2
    have unread := standard_not_read (instruction := instruction)
      (data := data.mapFamily pooledArithmeticFamily)
      (by simp [pooledDecoderFields, standard])
    rw [unread]
    have quotient : data.mask / 256 = 0 := Nat.div_eq_of_lt (by omega)
    simp [Nat.testBit, Nat.shiftRight_eq_div_pow, quotient]
  · obtain ⟨rd, nonzero, rfl, rfl⟩ := h
    simp [NonDeterminism.instructionRead, Nat.testBit, Nat.shiftRight_eq_div_pow]
    exact nonzero
  · obtain ⟨rs1, _, rfl, rfl⟩ := h
    simp [NonDeterminism.instructionRead, Nat.testBit, Nat.shiftRight_eq_div_pow]

private theorem addsub_read_flag {p : Nat} [Fact p.Prime] (hp : limbBase < p)
    {trace : PooledTrace p} (accepted : Accepted trace) {w : Nat → ZMod p}
    (member : (⟨.addSub, w⟩ : Row p PooledFamily) ∈ trace.rows)
    {entry : PooledProgramEntry} (small : entry.data.mask < 512)
    (query : (⟨.addSub, w⟩ : Row p PooledFamily).decoderQuery = entry.query) :
    isRead (⟨.addSub, w⟩ : Row p PooledFamily) = entry.data.mask.testBit 8 := by
  let original : ProgramEntry := ⟨entry.pc, entry.bits, entry.instruction,
    entry.data.mapFamily (fun _ => .addSub)⟩
  have flags := row_query_selectors_of_bound hp trace.rom.wordMemory
    (row := ⟨.addSub, w⟩) (entry := original) (accepted.constraints _ member) small query
  have selected := flags ⟨8, by change 8 < 9; decide⟩
  change w 18 = if entry.data.mask.testBit 8 then 1 else 0 at selected
  simp only [isRead, NonDeterminism.isRead, selected]
  cases entry.data.mask.testBit 8 <;> simp

theorem read_classification {p : Nat} [Fact p.Prime] (hp : limbBase < p)
    {trace : PooledTrace p} (accepted : Accepted trace) {row : Row p PooledFamily}
    (member : row ∈ trace.rows) {entry : PooledProgramEntry}
    (fields : Pooled.decoderFields entry.instruction = some entry.data)
    (family : entry.data.family = row.family) (query : row.decoderQuery = entry.query) :
    isRead row = NonDeterminism.instructionRead entry.instruction := by
  rcases fields_cases fields with ⟨original, selected, equal⟩ | standard
  · have classified := restricted_read selected
    have bound := (NonDeterminism.Proofs.field_bounds selected).2
    cases row with
    | mk kind w =>
      cases mode : original.family <;>
        simp only [equal, DecoderData.mapFamily, mode, pooledArithmeticFamily] at family
      · subst kind
        exact (addsub_read_flag hp accepted member
          (by simpa [equal, DecoderData.mapFamily] using bound) query).trans
          (by simpa [equal, DecoderData.mapFamily] using classified)
      · subst kind
        have nonread : original.mask.testBit 8 = false := by
          have load := NonDeterminism.Proofs.fields_cases selected
          rcases load with h | ⟨rd, _, _, data⟩ | ⟨rs1, _, _, data⟩
          · have small := (decoder_field_bounds h).2
            have quotient : original.mask / 256 = 0 := Nat.div_eq_of_lt (by omega)
            simp [Nat.testBit, Nat.shiftRight_eq_div_pow, quotient]
          · rw [data] at mode; cases mode
          · rw [data] at mode; cases mode
        simp only [isRead, ← classified, nonread]
  · have unread := standard_not_read standard
    rw [unread]
    cases row with
    | mk kind w =>
      cases kind with
      | addSub =>
        have bound := standard_mask standard family
        have selected := addsub_read_flag hp accepted member (by omega) query
        have quotient : entry.data.mask / 256 = 0 := Nat.div_eq_of_lt bound
        simpa [Nat.testBit, Nat.shiftRight_eq_div_pow, quotient] using selected
      | wordMemory | jumpBranchSlt | mulDiv | shiftBinop | subwordMemory => rfl

theorem decoder_soundness {p : Nat} [Fact p.Prime] (hp : limbBase < p)
    {trace : PooledTrace p} (accepted : Accepted trace)
    {before : Reference.RiscV.Sail.State} {addresses : List (BitVec 32)}
    {program : List PooledProgramEntry} (image : Pooled.programImage before addresses = some program)
    (decoded : PooledDecoded trace program) :
    ∀ row ∈ trace.rows, Fetched row before := by
  intro row member
  obtain ⟨entry, present, family, query⟩ := decoder_member (decoded row member)
  have source := run_program_sources image entry present
  have fetched := native_query_pc_word hp query
  change row.start.word = Word.ofBitVec entry.pc at fetched
  refine ⟨entry, source, family, query, ?_,
    read_classification hp accepted member source.fields family query⟩
  rw [fetched, Word.ofBitVec_roundtrip]

instance oraclePooledRegistry : PooledRegistry Pooled.decoderFields where
  arithmeticProjection := NonDeterminism.decoderFields
  rules := NonDeterminism.Proofs.decoderRules
  memoryFields := NonDeterminism.Proofs.memory_fields
  sourceCases := source_cases

end Airbender.Trace.NonDeterminism.Pooled.Proofs
