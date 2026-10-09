import Airbender.Proofs.Trace.PooledOracleDecoder
import Airbender.Proofs.Trace.PooledHistory

namespace Airbender.Trace.NonDeterminism.Pooled.Proofs
open Arithmetic Trace.Proofs

theorem zero_preserving {p : Nat} [Fact p.Prime] (hp : 196608 < p)
    {trace : PooledTrace p} (accepted : Accepted trace)
    {before : Reference.RiscV.Sail.State} {addresses : List (BitVec 32)}
    {program : List PooledProgramEntry} (image : Pooled.programImage before addresses = some program)
    (decoded : PooledDecoded trace program) : ZeroPreserving trace := by
  intro row member
  obtain ⟨entry, present, family, query⟩ := decoder_member (decoded row member)
  have source := run_program_sources image entry present
  exact pooled_row_zero_preserving NonDeterminism.Proofs.decoderRules hp trace.rom row
    (accepted.constraints row member) (source_cases source) family query

theorem write_rules {p : Nat} [Fact p.Prime] (hp : 33554432 < p)
    {trace : PooledTrace p} (accepted : Accepted trace)
    {before : Reference.RiscV.Sail.State} {cells : List Cell}
    (image : initialImage before cells = some trace.initialMemory)
    (wordSetup : trace.rom.wordMemory = ROM.table cells trace.initialMemory)
    {values : Nat → BitVec 32} (subwordSetup : trace.rom.subwordMemory = Verification.subwordTable values)
    {addresses : List (BitVec 32)} {program : List PooledProgramEntry}
    (programImage : Pooled.programImage before addresses = some program)
    (decoded : PooledDecoded trace program) : WriteBoundsFromReads trace := by
  intro row member
  obtain ⟨entry, present, family, query⟩ := decoder_member (decoded row member)
  have source := run_program_sources programImage entry present
  exact pooled_row_write_rule hp (accepted.constraints row member) (accepted.active row member)
    image wordSetup subwordSetup (source_cases source) family query

theorem native_history {p : Nat} [Fact p.Prime]
    (hp : 2 * timestampBase + 4 < p) (inverse : (-3840 : ZMod p) * 524288 = 1)
    {trace : PooledTrace p} (accepted : Accepted trace) (clocks : ClockBoundary trace)
    {before : Reference.RiscV.Sail.State} {cells : List Cell}
    (image : initialImage before cells = some trace.initialMemory)
    (distinct : cells.Nodup) (aligned : ∀ cell ∈ cells, cell.Aligned)
    {addresses : List (BitVec 32)} {program : List PooledProgramEntry}
    (programImage : Pooled.programImage before addresses = some program)
    (decoded : PooledDecoded trace program) :
    ∃ (history : TimestampSortedMemoryAccessList) (rows : List (Row p PooledFamily))
      (after : Reference.RiscV.Sail.State),
      MemoryHistory trace history ∧ rows.Perm trace.rows ∧
      rows.Pairwise (fun a b => b.clock < a.clock) ∧
      SailHistory cells (rows.flatMap fun row => (rowEvents trace.memoryEpoch row).reverse) before after ∧
      SailStateMatches cells history after := by
  have preserves := zero_preserving (by dsimp [timestampBase] at hp; omega)
    accepted programImage decoded
  exact native_row_history hp inverse accepted clocks image distinct aligned
    (zero_writes_of_preserving hp inverse accepted clocks image preserves)

theorem value_bounds {p : Nat} [Fact p.Prime] (hp : 33554432 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1)
    {trace : PooledTrace p} (accepted : Accepted trace) (clocks : ClockBoundary trace)
    {before : Reference.RiscV.Sail.State} {cells : List Cell}
    (image : initialImage before cells = some trace.initialMemory)
    (wordSetup : trace.rom.wordMemory = ROM.table cells trace.initialMemory)
    {values : Nat → BitVec 32} (subwordSetup : trace.rom.subwordMemory = Verification.subwordTable values)
    {addresses : List (BitVec 32)} {program : List PooledProgramEntry}
    (programImage : Pooled.programImage before addresses = some program)
    (decoded : PooledDecoded trace program) :
    (∀ row ∈ trace.rows, ∀ port ∈ row.ports, (readToken row.assignment port).word.Bounded) ∧
    (∀ row ∈ trace.rows, ∀ port ∈ row.ports,
      (writeToken row.columns row.assignment port).word.Bounded) ∧
    (∀ token ∈ trace.terminalMemory, token.word.Bounded) := by
  have rules := write_rules hp accepted image wordSetup subwordSetup programImage decoded
  have clockField : 2 * timestampBase + 4 < p := by dsimp [timestampBase]; omega
  have seed := image_bounds image
  exact ⟨read_bounds_of_rules clockField inverse accepted clocks seed rules,
    write_bounds_of_rules clockField inverse accepted clocks seed rules,
    terminal_bounds_of_rules clockField inverse accepted clocks seed rules⟩

end Airbender.Trace.NonDeterminism.Pooled.Proofs
