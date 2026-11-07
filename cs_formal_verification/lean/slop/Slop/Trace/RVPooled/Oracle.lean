import Human.Helpers.Decoder.RVExternalInput
import Slop.Trace.RVPooled.Arithmetic
import Slop.Trace.RVZeroPooled
import Slop.Trace.RVValuesPooled

/-! The six-family registry extended with the CSR 0x7C0 forms (`NonDeterminism.Pooled.rvDecoderFields`): its cases
    (the read row, the write row = the NOP row, or the standard table), its x0 decoder rules, and the pooled x0 and
    value-bound laws for programs built with it. A read row is an ADD/SUB row with selector 8 writing `rd`. -/

namespace Airbender.Trace.Proofs
open Arithmetic

/-- The CSR 0x7C0 read row's metadata. -/
abbrev rvReadData (rd : BitVec 5) : DecoderData := ⟨.addSub, 0, 0, rd, ⟨0, 0⟩, 256, 0⟩

/-- The extended projection's cases: a read, a write (the NOP row), or the standard table. -/
theorem rv_oracle_fields_cases {i : RV.Instr} {data : DecoderData PooledFamily}
    (fields : NonDeterminism.Pooled.rvDecoderFields i = some data) :
    (∃ rd, rd ≠ 0 ∧ i = .inputRead rd ∧ data = (rvReadData rd).mapFamily pooledArithmeticFamily) ∨
    (∃ src, i = .inputWrite src ∧ data = rvNopData.mapFamily pooledArithmeticFamily) ∨
    rvPooledDecoderFields i = some data := by
  unfold NonDeterminism.Pooled.rvDecoderFields NonDeterminism.rvDecoderFields at fields
  split at fields
  · rename_i rd
    split at fields
    · exact Or.inr (Or.inr (by simpa using fields))
    · exact Or.inl ⟨rd, by assumption, rfl, by simpa [rvReadData] using fields.symm⟩
  · exact Or.inr (Or.inl ⟨_, rfl, by simpa [rvNopData] using fields.symm⟩)
  · refine Or.inr (Or.inr ?_)
    cases h : Trace.rvDecoderFields i with
    | none => simpa [h] using fields
    | some d =>
      have eq : some (d.mapFamily pooledArithmeticFamily) = some data := by simpa [h] using fields
      unfold rvPooledDecoderFields
      rw [h]
      exact eq

/-- The x0 decoder rules of the extended arithmetic projection. -/
theorem rvOracleDecoderRules : RVDecoderRules NonDeterminism.rvDecoderFields where
  bounds i data fields := by
    unfold NonDeterminism.rvDecoderFields at fields
    split at fields
    · split at fields
      · cases fields
      · obtain rfl := Option.some.inj fields
        exact ⟨by constructor <;> show (0 : Nat) < limbBase <;> decide, by show (256 : Nat) < 512; decide⟩
    · obtain rfl := Option.some.inj fields
      exact ⟨by constructor <;> decide, by decide⟩
    · exact rvStandardDecoderRules.bounds _ _ fields
  zeroNop i data fields family zero := by
    unfold NonDeterminism.rvDecoderFields at fields
    split at fields
    · split at fields
      · cases fields
      · obtain rfl := Option.some.inj fields
        exact absurd zero (by assumption)
    · exact (Option.some.inj fields).symm
    · exact rvStandardDecoderRules.zeroNop _ _ fields family zero
  loadNonzero i data fields family load := by
    unfold NonDeterminism.rvDecoderFields at fields
    split at fields
    · split at fields
      · cases fields
      · obtain rfl := Option.some.inj fields
        cases family
    · obtain rfl := Option.some.inj fields
      cases family
    · exact rvStandardDecoderRules.loadNonzero _ _ fields family load

/-- The row of an extended entry with read or write metadata is an ADD/SUB row. -/
theorem rv_oracle_addsub {p : Nat} {row : Row p PooledFamily} {d : DecoderData}
    {entry : RVPooledProgramEntry} (family : entry.data.family = row.family)
    (data : entry.data = d.mapFamily pooledArithmeticFamily) (tag : d.family = .addSub) :
    row.family = .addSub := by
  rw [← family, data]
  simp [DecoderData.mapFamily, tag, pooledArithmeticFamily]

/-- Every row of an accepted trace decoded against an extended program preserves x0. -/
theorem rv_oracle_zero_preserving {p : Nat} [Fact p.Prime] (hp : 196608 < p)
    {trace : PooledTrace p} (accepted : Accepted trace)
    {initial : RV.State} {addresses : List (BitVec 32)} {program : List RVPooledProgramEntry}
    (image : rvProgramImageWith NonDeterminism.Pooled.rvDecoderFields initial addresses = some program)
    (decoded : RVPooledDecoded trace program) : ZeroPreserving trace := by
  have limbField : limbBase < p := by dsimp [limbBase]; omega
  intro row member
  obtain ⟨entry, present, family, query⟩ := rv_decoder_member (decoded row member)
  obtain ⟨_, _, i, _, fields⟩ := rvProgram_entry_fetch image entry present
  rcases rv_oracle_fields_cases fields with ⟨rd, nonzero, rfl, data⟩ | ⟨src, rfl, data⟩ | standard
  · have tag := rv_oracle_addsub family data rfl
    obtain ⟨kind, w⟩ := row
    change kind = .addSub at tag
    subst tag
    obtain ⟨pc, bits, entryData⟩ := entry
    change entryData = _ at data
    subst data
    have query' : (⟨.addSub, w⟩ : Row p).decoderQuery = (⟨pc, bits, rvReadData rd⟩ : RVProgramEntry).query := query
    have fetch : RVZero.RVFetched (⟨.addSub, w⟩ : Row p) NonDeterminism.rvDecoderFields :=
      ⟨⟨pc, bits, rvReadData rd⟩, .inputRead rd,
        by simp only [NonDeterminism.rvDecoderFields, if_neg nonzero], rfl, query',
        rv_row_query_selectors_of_bound limbField trace.rom.wordMemory (accepted.constraints _ member)
          (show (256 : Nat) < 512 by decide) query'⟩
    exact RVZero.row_zero_write_from_reads rvOracleDecoderRules hp ⟨.addSub, w⟩ trace.rom.wordMemory
      (accepted.constraints _ member) fetch
  · exact RVZero.rv_pooled_row_zero_preserving hp trace.rom row (accepted.constraints row member)
      (i := .op .add 0 0 0) (by rw [data]; rfl) family query
  · exact RVZero.rv_pooled_row_zero_preserving hp trace.rom row (accepted.constraints row member) standard
      family query

/-- Every row's write rule, for an extended program. -/
theorem rv_oracle_write_rules {p : Nat} [Fact p.Prime] (hp : 33554432 < p)
    {trace : PooledTrace p} (accepted : Accepted trace)
    {initial : RV.State} {cells : List Cell}
    (wordSetup : trace.rom.wordMemory = ROM.table cells (romImageRV initial cells))
    {values : Nat → BitVec 32} (subwordSetup : trace.rom.subwordMemory = Verification.subwordTable values)
    {addresses : List (BitVec 32)} {program : List RVPooledProgramEntry}
    (programImage : rvProgramImageWith NonDeterminism.Pooled.rvDecoderFields initial addresses = some program)
    (decoded : RVPooledDecoded trace program) : WriteBoundsFromReads trace := by
  have limbField : limbBase < p := by dsimp [limbBase]; omega
  intro row member
  obtain ⟨entry, present, family, query⟩ := rv_decoder_member (decoded row member)
  obtain ⟨_, _, i, _, fields⟩ := rvProgram_entry_fetch programImage entry present
  have addsub (tag : row.family = .addSub) : RowWriteBoundsFromReads row := by
    obtain ⟨kind, w⟩ := row
    change kind = .addSub at tag
    subst tag
    apply row_write_rule_of_sources
    exact row_write_source ⟨.addSub, w⟩ trace.rom.wordMemory (accepted.constraints _ member)
      (fun query h inactive => RVValues.rv_rom_disabled (by omega) (by rwa [wordSetup] at h) inactive)
      (fun query h => RVValues.rv_rom_bounds limbField (by rwa [wordSetup] at h))
  rcases rv_oracle_fields_cases fields with ⟨rd, -, -, data⟩ | ⟨src, -, data⟩ | standard
  · exact addsub (rv_oracle_addsub family data rfl)
  · exact addsub (rv_oracle_addsub family data rfl)
  · exact RVValues.rv_pooled_row_write_rule hp (accepted.constraints row member) (accepted.active row member)
      wordSetup subwordSetup standard family query

/-- One RV public image and an extended program table bound every native read, write and terminal word. -/
theorem rv_oracle_value_bounds {p : Nat} [Fact p.Prime] (hp : 33554432 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1)
    {trace : PooledTrace p} (accepted : Accepted trace) (clocks : ClockBoundary trace)
    {initial : RV.State} {cells : List Cell}
    (image : initialImageRV initial cells = some trace.initialMemory)
    (wordSetup : trace.rom.wordMemory = ROM.table cells (romImageRV initial cells))
    {values : Nat → BitVec 32} (subwordSetup : trace.rom.subwordMemory = Verification.subwordTable values)
    {addresses : List (BitVec 32)} {program : List RVPooledProgramEntry}
    (programImage : rvProgramImageWith NonDeterminism.Pooled.rvDecoderFields initial addresses = some program)
    (decoded : RVPooledDecoded trace program) :
    ∀ row ∈ trace.rows, ∀ port ∈ row.ports, (readToken row.assignment port).word.Bounded := by
  have rules := rv_oracle_write_rules hp accepted wordSetup subwordSetup programImage decoded
  have clockField : 2 * timestampBase + 4 < p := by dsimp [timestampBase]; omega
  exact read_bounds_of_rules clockField inverse accepted clocks (RVValues.rv_image_bounds image) rules

end Airbender.Trace.Proofs
