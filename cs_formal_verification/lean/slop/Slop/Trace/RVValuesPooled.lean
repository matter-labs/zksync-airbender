module
public import Slop.JumpBranchSlt.RVValues
public import Slop.ShiftBinop.RVValues
public import Slop.MulDiv.Values
public import Slop.SubwordMemory.Values
public import Slop.Trace.Family.Values
public import Slop.Trace.Pooled
public import Slop.Trace.RVProgram
public import Slop.Trace.RVValues

@[expose] public section

/-! The pooled RV value-bounds law: the family write rules assembled over the pooled decoder projection. -/

namespace Airbender.Trace.RVValues
open Arithmetic Trace.Proofs

/-- RV twin of `pooled_row_write_rule`: the RV projection equation replaces `PooledSource`, and the word ROM is
    built from the ROM image (`romImageRV`). -/
theorem rv_pooled_row_write_rule {p : Nat} [Fact p.Prime] (hp : 33554432 < p)
    {trace : PooledTrace p} {row : Row p PooledFamily}
    (constraints : FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment)
      (row.constraints trace.rom))
    (active : row.assignment row.columns.execute = 1)
    {before : RV.State} {cells : List Cell}
    (wordSetup : trace.rom.wordMemory = ROM.table cells (romImageRV before cells))
    {values : Nat → BitVec 32}
    (subwordSetup : trace.rom.subwordMemory = Verification.subwordTable values)
    {entry : RVPooledProgramEntry} {i : RV.Instr} (fields : rvPooledDecoderFields i = some entry.data)
    (family : entry.data.family = row.family) (query : row.decoderQuery = entry.query) :
    RowWriteBoundsFromReads row := by
  have limbField : limbBase < p := by dsimp [limbBase]; omega
  obtain ⟨pc, bits, data⟩ := entry
  obtain h | h | h | h | h := rv_pooled_fields_cases fields
  · obtain ⟨d, fd, equal⟩ := h
    subst equal
    cases row with
    | mk kind w =>
      cases mode : d.family
      all_goals simp only [DecoderData.mapFamily, mode, pooledArithmeticFamily] at family
      all_goals subst kind
      all_goals apply row_write_rule_of_sources
      · exact row_write_source ⟨.addSub, w⟩ trace.rom.wordMemory constraints
          (fun query h inactive => rv_rom_disabled (by omega)
            (by rwa [wordSetup] at h) inactive)
          (fun query h => rv_rom_bounds limbField (by rwa [wordSetup] at h))
      · exact row_write_source ⟨.wordMemory, w⟩ trace.rom.wordMemory constraints
          (fun query h inactive => rv_rom_disabled (by omega)
            (by rwa [wordSetup] at h) inactive)
          (fun query h => rv_rom_bounds limbField (by rwa [wordSetup] at h))
  · obtain ⟨d, fd, equal⟩ := h
    subst equal
    cases row with
    | mk kind w =>
      change PooledFamily.jumpBranchSlt = kind at family
      subst kind
      have core := Verification.holds_of_sublist constraints
        (List.sublist_append_left JumpBranchSlt.importedConstraints JumpBranchSlt.importedConstraintsTimestampLookups)
      have bounds := JumpBranchSlt.Proofs.rv_decoder_field_bounds fd
      have query' : JumpBranchSlt.decoderQuery w = (⟨pc, bits, d⟩ : RVProgramEntry Unit).query := query
      have flags := JumpBranchSlt.Proofs.rv_decoder_selectors limbField core bounds.2.1 query'
      have pc := rv_native_query_pc_word limbField query
      have low : (w 0).val < limbBase := by
        have bounds := pc.symm ▸ Word.ofBitVec_bound _
        exact bounds.1
      exact row_write_rule_of_sources
        (JumpBranchSlt.Proofs.rv_row_write_sources (by omega) ⟨.jumpBranchSlt, w⟩ core fd flags low)
  · obtain ⟨d, fd, equal⟩ := h
    subst equal
    cases row with
    | mk kind w =>
      change PooledFamily.mulDiv = kind at family
      subst kind
      have core := Verification.holds_of_sublist constraints
        (List.sublist_append_left MulDiv.importedConstraints MulDiv.importedConstraintsTimestampLookups)
      exact row_write_rule_of_sources (MulDiv.Proofs.row_write_sources ⟨.mulDiv, w⟩ core)
  · obtain ⟨d, fd, equal⟩ := h
    subst equal
    cases row with
    | mk kind w =>
      change PooledFamily.shiftBinop = kind at family
      subst kind
      have core := Verification.holds_of_sublist constraints
        (List.sublist_append_left ShiftBinop.importedConstraints ShiftBinop.importedConstraintsTimestampLookups)
      exact row_write_rule_of_sources
        (ShiftBinop.Proofs.rv_row_write_sources (entry := ⟨pc, bits, d⟩) (by omega)
          ⟨.shiftBinop, w⟩ core fd query)
  · obtain ⟨d, fd, equal⟩ := h
    subst equal
    cases row with
    | mk kind w =>
      change PooledFamily.subwordMemory = kind at family
      subst kind
      have core := Verification.holds_of_sublist constraints
        (List.sublist_append_left (SubwordMemory.importedConstraints trace.rom.subwordMemory)
          SubwordMemory.importedConstraintsTimestampLookups)
      rw [subwordSetup] at core
      exact SubwordMemory.Proofs.row_write_rule hp ⟨.subwordMemory, w⟩ core active

/-- RV twin of `pooled_write_rules`: every row's write rule, from the RV program table. -/
theorem rv_pooled_write_rules {p : Nat} [Fact p.Prime] (hp : 33554432 < p)
    {trace : PooledTrace p} (accepted : Accepted trace)
    {initial : RV.State} {cells : List Cell}
    (wordSetup : trace.rom.wordMemory = ROM.table cells (romImageRV initial cells))
    {values : Nat → BitVec 32} (subwordSetup : trace.rom.subwordMemory = Verification.subwordTable values)
    {addresses : List (BitVec 32)} {program : List RVPooledProgramEntry}
    (programImage : rvProgramImageWith rvPooledDecoderFields initial addresses = some program)
    (decoded : RVPooledDecoded trace program) : WriteBoundsFromReads trace := by
  intro row member
  obtain ⟨entry, present, family, query⟩ := rv_decoder_member (decoded row member)
  obtain ⟨_, _, _, _, fields⟩ := rvProgram_entry_fetch programImage entry present
  exact rv_pooled_row_write_rule hp (accepted.constraints row member) (accepted.active row member)
    wordSetup subwordSetup fields family query

/-- RV twin of `pooled_value_bounds`: one RV public image and program table bound every native read, write and
    terminal word. -/
theorem rv_pooled_value_bounds {p : Nat} [Fact p.Prime] (hp : 33554432 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1)
    {trace : PooledTrace p} (accepted : Accepted trace) (clocks : ClockBoundary trace)
    {initial : RV.State} {cells : List Cell}
    (image : initialImageRV initial cells = some trace.initialMemory)
    (wordSetup : trace.rom.wordMemory = ROM.table cells (romImageRV initial cells))
    {values : Nat → BitVec 32} (subwordSetup : trace.rom.subwordMemory = Verification.subwordTable values)
    {addresses : List (BitVec 32)} {program : List RVPooledProgramEntry}
    (programImage : rvProgramImageWith rvPooledDecoderFields initial addresses = some program)
    (decoded : RVPooledDecoded trace program) :
    (∀ row ∈ trace.rows, ∀ port ∈ row.ports, (readToken row.assignment port).word.Bounded) ∧
    (∀ row ∈ trace.rows, ∀ port ∈ row.ports,
      (writeToken row.columns row.assignment port).word.Bounded) ∧
    (∀ token ∈ trace.terminalMemory, token.word.Bounded) := by
  have rules := rv_pooled_write_rules hp accepted wordSetup subwordSetup programImage decoded
  have clockField : 2 * timestampBase + 4 < p := by dsimp [timestampBase]; omega
  have seed := rv_image_bounds image
  exact ⟨read_bounds_of_rules clockField inverse accepted clocks seed rules,
    write_bounds_of_rules clockField inverse accepted clocks seed rules,
    terminal_bounds_of_rules clockField inverse accepted clocks seed rules⟩

end Airbender.Trace.RVValues
