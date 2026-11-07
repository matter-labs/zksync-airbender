import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Review.Helpers.Core.SerializedInverse
import Airbender.Proofs.Trace.PooledValues
import Airbender.Proofs.Trace.RowHistory

namespace Airbender.Trace.Proofs
open Arithmetic

theorem pooled_row_zero_preserving {p : Nat} [Fact p.Prime]
    {arithmeticProjection : SailRV32.instruction → Option DecoderData}
    (rules : DecoderRules arithmeticProjection) (hp : FieldCapacity.NoWrap p 196608)
    (setup : PooledSetup p) (row : Row p PooledFamily)
    (constraints : FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment)
      (row.constraints setup))
    {before : Reference.RiscV.Sail.State} {entry : PooledProgramEntry}
    (source : PooledSource before entry arithmeticProjection)
    (family : entry.data.family = row.family) (query : row.decoderQuery = entry.query) :
    RowZeroPreserving row := by
  have limbField : limbBase < p := by dsimp [limbBase]; omega
  obtain original | original | original | original | original := source
  all_goals obtain ⟨originalEntry, originalSource, equal⟩ := original
  all_goals subst entry
  all_goals rw [mapped_query] at query
  · cases row with
    | mk kind w =>
      cases mode : originalEntry.data.family
      all_goals simp only [ProgramEntry.mapFamily, DecoderData.mapFamily, mode,
        pooledArithmeticFamily] at family
      all_goals subst kind
      all_goals
        have pc := native_query_pc_word limbField query
        have mask : originalEntry.data.mask < 512 := by
          have bound := (rules.bounds _ _ originalSource.fields).2
          omega
      · have fetch : (⟨.addSub, w⟩ : Row p).Fetched before arithmeticProjection :=
          ⟨originalEntry, originalSource, mode, query,
            (congrArg Word.toBitVec pc).trans (Word.ofBitVec_roundtrip _),
            row_query_selectors_of_bound limbField setup.wordMemory constraints mask query⟩
        exact row_zero_write_from_reads rules hp ⟨.addSub, w⟩
          setup.wordMemory constraints fetch
      · have fetch : (⟨.wordMemory, w⟩ : Row p).Fetched before arithmeticProjection :=
          ⟨originalEntry, originalSource, mode, query,
            (congrArg Word.toBitVec pc).trans (Word.ofBitVec_roundtrip _),
            row_query_selectors_of_bound limbField setup.wordMemory constraints mask query⟩
        exact row_zero_write_from_reads rules hp ⟨.wordMemory, w⟩
          setup.wordMemory constraints fetch
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
      exact JumpBranchSlt.Proofs.row_zero_preserving limbField ⟨.jumpBranchSlt, w⟩ core fetch
  · cases row with
    | mk kind w =>
      change PooledFamily.mulDiv = kind at family
      subst kind
      exact MulDiv.Proofs.row_zero_preserving limbField ⟨.mulDiv, w⟩ originalSource query
  · cases row with
    | mk kind w =>
      change PooledFamily.shiftBinop = kind at family
      subst kind
      exact ShiftBinop.Proofs.row_zero_preserving limbField ⟨.shiftBinop, w⟩ originalSource query
  · cases row with
    | mk kind w =>
      change PooledFamily.subwordMemory = kind at family
      subst kind
      have core := Verification.holds_of_sublist constraints
        (List.sublist_append_left (SubwordMemory.importedConstraints setup.subwordMemory)
          SubwordMemory.importedConstraintsTimestampLookups)
      exact SubwordMemory.Proofs.row_zero_preserving limbField ⟨.subwordMemory, w⟩
        setup.subwordMemory core originalSource query

/-- Native x0 semantics propagate through the same history across all six
    families. Actual decoding supplies preprocessing and destination exclusion. -/
theorem pooled_zero_preserving {p : Nat} [Fact p.Prime]
    {projection : SailRV32.instruction → Option (DecoderData PooledFamily)}
    [registry : PooledRegistry projection] (hp : FieldCapacity.NoWrap p 196608)
    {trace : PooledTrace p} (accepted : Accepted trace)
    {before : Reference.RiscV.Sail.State} {addresses : List (BitVec 32)}
    {program : List PooledProgramEntry} (image : programImageRunWith projection before addresses = some program)
    (decoded : PooledDecoded trace program) : ZeroPreserving trace := by
  intro row member
  obtain ⟨entry, present, family, query⟩ := decoder_member (decoded row member)
  have source := run_program_sources image entry present
  exact pooled_row_zero_preserving registry.rules hp trace.rom row
    (accepted.constraints row member) (registry.sourceCases source) family query

/-- One globally initialized history is realized by actual Sail cell reads and
    writes, in the derived instruction order. This adds no expected-read premise.
    Original ISA-clause retirement is proved separately from cell transport. -/
theorem pooled_native_history {p : Nat} [Fact p.Prime]
    {projection : SailRV32.instruction → Option (DecoderData PooledFamily)}
    [registry : PooledRegistry projection]
    (hp : FieldCapacity.ClockNoWrap p timestampBase) (inverse : SerializedInverse.Clock p)
    {trace : PooledTrace p} (accepted : Accepted trace) (clocks : ClockBoundary trace)
    {before : Reference.RiscV.Sail.State} {cells : List Cell}
    (image : initialImage before cells = some trace.initialMemory)
    (distinct : cells.Nodup) (aligned : ∀ cell ∈ cells, cell.Aligned)
    {addresses : List (BitVec 32)} {program : List PooledProgramEntry}
    (programImage : programImageRunWith projection before addresses = some program)
    (decoded : PooledDecoded trace program) :
    ∃ (history : TimestampSortedMemoryAccessList) (rows : List (Row p PooledFamily))
      (after : Reference.RiscV.Sail.State),
      MemoryHistory trace history ∧ rows.Perm trace.rows ∧
      rows.Pairwise (fun a b => b.clock < a.clock) ∧
      SailHistory cells (rows.flatMap fun row => (rowEvents trace.memoryEpoch row).reverse) before after ∧
      SailStateMatches cells history after := by
  have preserves := pooled_zero_preserving (by dsimp [timestampBase] at hp; omega)
    accepted programImage decoded
  exact native_row_history hp inverse accepted clocks image distinct aligned
    (zero_writes_of_preserving hp inverse accepted clocks image preserves)

end Airbender.Trace.Proofs
