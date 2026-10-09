import Airbender.Proofs.Trace.Pooled
import Airbender.Proofs.Trace.PooledProgram
import Airbender.Proofs.Trace.ROM
import Airbender.Proofs.JumpBranchSlt.Values
import Airbender.Proofs.MulDiv.Values
import Airbender.Proofs.ShiftBinop.Values
import Airbender.Proofs.SubwordMemory.Values

namespace Airbender.Trace.Proofs
open Arithmetic

/-- Dispatch only the local imported write laws. Bounds of operands are supplied
    by the shared chronological induction, including cross-family dependencies. -/
theorem pooled_write_rules {p : Nat} [Fact p.Prime] (hp : 33554432 < p)
    {trace : PooledTrace p} (accepted : Accepted trace)
    {before : Reference.RiscV.Sail.State} {cells : List Cell}
    (image : initialImage before cells = some trace.initialMemory)
    (wordSetup : trace.rom.wordMemory = ROM.table cells trace.initialMemory)
    {values : Nat → BitVec 32} (subwordSetup : trace.rom.subwordMemory = Verification.subwordTable values)
    {addresses : List (BitVec 32)} {program : List PooledProgramEntry}
    (programImage : pooledProgramImage before addresses = some program)
    (decoded : PooledDecoded trace program) : WriteBoundsFromReads trace := by
  intro row member
  have limbField : limbBase < p := by dsimp [limbBase]; omega
  have constraints := accepted.constraints row member
  have active := accepted.active row member
  obtain ⟨entry, present, family, query⟩ := decoder_member (decoded row member)
  have source := run_program_sources programImage entry present
  obtain original | original | original | original | original := pooled_source_cases source
  all_goals obtain ⟨originalEntry, originalSource, equal⟩ := original
  all_goals subst entry
  all_goals rw [mapped_query] at query
  · cases row with
    | mk kind w =>
      cases mode : originalEntry.data.family
      all_goals simp only [ProgramEntry.mapFamily, DecoderData.mapFamily, mode,
        pooledArithmeticFamily] at family
      all_goals subst kind
      all_goals apply row_write_rule_of_sources
      · exact row_write_source ⟨.addSub, w⟩ trace.rom.wordMemory constraints
          (fun query h inactive => ROM.Proofs.disabled (by omega) image
            (by rwa [wordSetup] at h) inactive)
          (fun query h => ROM.Proofs.bounds limbField image (by rwa [wordSetup] at h))
      · exact row_write_source ⟨.wordMemory, w⟩ trace.rom.wordMemory constraints
          (fun query h inactive => ROM.Proofs.disabled (by omega) image
            (by rwa [wordSetup] at h) inactive)
          (fun query h => ROM.Proofs.bounds limbField image (by rwa [wordSetup] at h))
  · cases row with
    | mk kind w =>
      change PooledFamily.jumpBranchSlt = kind at family
      subst kind
      have core := Verification.holds_of_sublist constraints
        (List.sublist_append_left JumpBranchSlt.importedConstraints JumpBranchSlt.importedConstraintsTimestampLookups)
      have fields := JumpBranchSlt.Proofs.decoder_field_bounds originalSource.fields
      have fetch : JumpBranchSlt.Fetched w before :=
        ⟨originalEntry, originalSource, query, fields.1, fields.2.2,
          JumpBranchSlt.Proofs.decoder_selectors limbField core fields.2.1 query⟩
      have pc := native_query_pc_word limbField query
      have low : (w 0).val < limbBase := by
        have bounds := pc.symm ▸ Word.ofBitVec_bound originalEntry.pc
        exact bounds.1
      exact row_write_rule_of_sources
        (JumpBranchSlt.Proofs.row_write_sources (by omega) ⟨.jumpBranchSlt, w⟩ core fetch low)
  · cases row with
    | mk kind w =>
      change PooledFamily.mulDiv = kind at family
      subst kind
      have core := Verification.holds_of_sublist constraints
        (List.sublist_append_left MulDiv.importedConstraints MulDiv.importedConstraintsTimestampLookups)
      exact row_write_rule_of_sources (MulDiv.Proofs.row_write_sources ⟨.mulDiv, w⟩ core)
  · cases row with
    | mk kind w =>
      change PooledFamily.shiftBinop = kind at family
      subst kind
      have core := Verification.holds_of_sublist constraints
        (List.sublist_append_left ShiftBinop.importedConstraints ShiftBinop.importedConstraintsTimestampLookups)
      have fields := ShiftBinop.Proofs.decoder_field_bounds originalSource.fields
      have fetch : ShiftBinop.Fetched w before :=
        ⟨originalEntry, originalSource, query, ShiftBinop.Proofs.decoder_selectors limbField core fields.2.1 query⟩
      exact row_write_rule_of_sources
        (ShiftBinop.Proofs.row_write_sources (by omega) ⟨.shiftBinop, w⟩ core fetch)
  · cases row with
    | mk kind w =>
      change PooledFamily.subwordMemory = kind at family
      subst kind
      have core := Verification.holds_of_sublist constraints
        (List.sublist_append_left (SubwordMemory.importedConstraints trace.rom.subwordMemory)
          SubwordMemory.importedConstraintsTimestampLookups)
      rw [subwordSetup] at core
      exact SubwordMemory.Proofs.row_write_rule hp ⟨.subwordMemory, w⟩ core active

/-- One public image and one global history derive every native read, write and
    terminal word bound. No family supplies a separate operand-bound premise. -/
theorem pooled_value_bounds {p : Nat} [Fact p.Prime] (hp : 33554432 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1)
    {trace : PooledTrace p} (accepted : Accepted trace) (clocks : ClockBoundary trace)
    {before : Reference.RiscV.Sail.State} {cells : List Cell}
    (image : initialImage before cells = some trace.initialMemory)
    (wordSetup : trace.rom.wordMemory = ROM.table cells trace.initialMemory)
    {values : Nat → BitVec 32} (subwordSetup : trace.rom.subwordMemory = Verification.subwordTable values)
    {addresses : List (BitVec 32)} {program : List PooledProgramEntry}
    (programImage : pooledProgramImage before addresses = some program)
    (decoded : PooledDecoded trace program) :
    (∀ row ∈ trace.rows, ∀ port ∈ row.ports, (readToken row.assignment port).word.Bounded) ∧
    (∀ row ∈ trace.rows, ∀ port ∈ row.ports,
      (writeToken row.columns row.assignment port).word.Bounded) ∧
    (∀ token ∈ trace.terminalMemory, token.word.Bounded) := by
  have rules := pooled_write_rules hp accepted image wordSetup subwordSetup programImage decoded
  have clockField : 2 * timestampBase + 4 < p := by dsimp [timestampBase]; omega
  have seed := image_bounds image
  exact ⟨read_bounds_of_rules clockField inverse accepted clocks seed rules,
    write_bounds_of_rules clockField inverse accepted clocks seed rules,
    terminal_bounds_of_rules clockField inverse accepted clocks seed rules⟩

end Airbender.Trace.Proofs
