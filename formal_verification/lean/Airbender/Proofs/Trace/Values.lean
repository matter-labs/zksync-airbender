import Airbender.Review.Helpers.Memory.Values
import Airbender.Proofs.Trace.DecoderSetup
import Airbender.Proofs.Trace.MemoryOrigins
import Airbender.Proofs.Trace.PublicImage
import Airbender.Proofs.AddSub.Result

namespace Airbender.Trace.Proofs
open Arithmetic

theorem read_word (w : Nat → ZMod p) (port : MemoryPort) :
    (readToken w port).word = ⟨(port.readValue.evaluate w)[0].val, (port.readValue.evaluate w)[1].val⟩ := by
  simp [readToken, MemoryToken.word, MemoryPort.readCode, WordColumns.code]

theorem write_word (columns : TraceColumns) (w : Nat → ZMod p) (port : MemoryPort) :
    (writeToken columns w port).word =
      ⟨((port.writeValue.getD port.readValue).evaluate w)[0].val,
        ((port.writeValue.getD port.readValue).evaluate w)[1].val⟩ := by
  simp [writeToken, MemoryToken.word, MemoryPort.writeCode, WordColumns.code]

/-- Local artifact laws used by the shared history induction. They do not
    assert operand bounds; the induction supplies bounds of earlier reads. -/
def RowWriteSources {Kind : Type} [CircuitLayout Kind] [Fact p.Prime]
    (row : Row p Kind) : Prop :=
  ∀ port ∈ row.ports,
    (writeToken row.columns row.assignment port).word.Bounded ∨
      ∃ source ∈ row.ports,
        (writeToken row.columns row.assignment port).value = (readToken row.assignment source).value ∧
        (source.event row.columns row.assignment).1 ≤ (port.event row.columns row.assignment).1

def RowWriteBoundsFromReads {Kind : Type} [CircuitLayout Kind] [Fact p.Prime]
    (row : Row p Kind) : Prop :=
  ∀ port ∈ row.ports,
    (∀ source ∈ row.ports,
      (source.event row.columns row.assignment).1 ≤ (port.event row.columns row.assignment).1 →
      (readToken row.assignment source).word.Bounded) →
    (writeToken row.columns row.assignment port).word.Bounded

def WriteSources {Kind : Type} [CircuitLayout Kind] [Fact p.Prime]
    (trace : Data p Kind) : Prop := ∀ row ∈ trace.rows, RowWriteSources row

def WriteBoundsFromReads {Kind : Type} [CircuitLayout Kind] [Fact p.Prime]
    (trace : Data p Kind) : Prop := ∀ row ∈ trace.rows, RowWriteBoundsFromReads row

/-- Copy/local-bound rules instantiate the same preservation rule. -/
theorem row_write_rule_of_sources {Kind : Type} [CircuitLayout Kind] [Fact p.Prime]
    {row : Row p Kind} (sources : RowWriteSources row) : RowWriteBoundsFromReads row := by
  intro port present reads
  rcases sources port present with bound | copied
  · exact bound
  · obtain ⟨source, sourceMember, copied, order⟩ := copied
    have previous := reads source sourceMember order
    simpa only [MemoryToken.word, copied] using previous

theorem write_rules_of_sources {Kind : Type} [CircuitLayout Kind] [Fact p.Prime]
    {trace : Data p Kind} (sources : WriteSources trace) : WriteBoundsFromReads trace :=
  fun row member => row_write_rule_of_sources (sources row member)

/-- Shared time induction derives read bounds from public seeds and proved
    local write preservation. Every dependency precedes the current read. -/
theorem read_bounds_of_rules {Kind : Type} [CircuitLayout Kind] [Fact p.Prime]
    [ClockLaws Kind p] (hp : 2 * timestampBase + 4 < p)
    {trace : Data p Kind}
    (accepted : Accepted trace) (clocks : ClockBoundary trace)
    (initial : ∀ token ∈ trace.initialMemory, token.word.Bounded)
    (rules : WriteBoundsFromReads trace) :
    ∀ row ∈ trace.rows, ∀ port ∈ row.ports, (readToken row.assignment port).word.Bounded := by
  have bounded : ∀ time : Nat, ∀ row ∈ trace.rows, ∀ port ∈ row.ports,
      (port.event row.columns row.assignment).1 = time → (readToken row.assignment port).word.Bounded := by
    intro time
    induction time using Nat.strong_induction_on with
    | h time ih =>
      intro row member port portMember clock
      rcases earlier_write hp accepted clocks row member port portMember with seed | prior
      · exact initial _ seed
      · obtain ⟨writer, writerMember, source, sourceMember, same, earlier⟩ := prior
        have bounds := rules writer writerMember source sourceMember (by
          intro read readMember order
          have before : (read.event writer.columns writer.assignment).1 < time := by omega
          exact ih _ before writer writerMember read readMember rfl)
        exact same ▸ bounds
  intro row member port portMember
  exact bounded _ row member port portMember rfl

theorem write_bounds_of_rules {Kind : Type} [CircuitLayout Kind] [Fact p.Prime]
    [ClockLaws Kind p] (hp : 2 * timestampBase + 4 < p)
    {trace : Data p Kind}
    (accepted : Accepted trace) (clocks : ClockBoundary trace)
    (initial : ∀ token ∈ trace.initialMemory, token.word.Bounded)
    (rules : WriteBoundsFromReads trace) :
    ∀ row ∈ trace.rows, ∀ port ∈ row.ports,
      (writeToken row.columns row.assignment port).word.Bounded := by
  intro row member port present
  exact rules row member port present (fun read readMember _ =>
    read_bounds_of_rules hp accepted clocks initial rules row member read readMember)

theorem terminal_bounds_of_rules {Kind : Type} [CircuitLayout Kind] [Fact p.Prime]
    [ClockLaws Kind p] (hp : 2 * timestampBase + 4 < p)
    {trace : Data p Kind}
    (accepted : Accepted trace) (clocks : ClockBoundary trace)
    (initial : ∀ token ∈ trace.initialMemory, token.word.Bounded)
    (rules : WriteBoundsFromReads trace) :
    ∀ token ∈ trace.terminalMemory, token.word.Bounded := by
  intro token member
  have matched := accepted.memory.mem_iff.mpr (List.mem_append_left _ member)
  rcases List.mem_append.mp matched with seed | written
  · exact initial _ seed
  · obtain ⟨row, rowMember, tokenMember⟩ := List.mem_flatMap.mp written
    obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp tokenMember
    exact write_bounds_of_rules hp accepted clocks initial rules row rowMember port
      (by simpa using portMember)

-- Compatibility with existing family proofs; the induction above is shared.
theorem read_bounds_of_sources {Kind : Type} [CircuitLayout Kind] [Fact p.Prime]
    [ClockLaws Kind p] (hp : 2 * timestampBase + 4 < p)
    {trace : Data p Kind}
    (accepted : Accepted trace) (clocks : ClockBoundary trace)
    (initial : ∀ token ∈ trace.initialMemory, token.word.Bounded) (sources : WriteSources trace) :
    ∀ row ∈ trace.rows, ∀ port ∈ row.ports, (readToken row.assignment port).word.Bounded :=
  read_bounds_of_rules hp accepted clocks initial (write_rules_of_sources sources)

theorem write_bounds_of_sources {Kind : Type} [CircuitLayout Kind] [Fact p.Prime]
    [ClockLaws Kind p] (hp : 2 * timestampBase + 4 < p)
    {trace : Data p Kind}
    (accepted : Accepted trace) (clocks : ClockBoundary trace)
    (initial : ∀ token ∈ trace.initialMemory, token.word.Bounded) (sources : WriteSources trace) :
    ∀ row ∈ trace.rows, ∀ port ∈ row.ports, (writeToken row.columns row.assignment port).word.Bounded :=
  write_bounds_of_rules hp accepted clocks initial (write_rules_of_sources sources)

theorem terminal_bounds_of_sources {Kind : Type} [CircuitLayout Kind] [Fact p.Prime]
    [ClockLaws Kind p] (hp : 2 * timestampBase + 4 < p)
    {trace : Data p Kind}
    (accepted : Accepted trace) (clocks : ClockBoundary trace)
    (initial : ∀ token ∈ trace.initialMemory, token.word.Bounded) (sources : WriteSources trace) :
    ∀ token ∈ trace.terminalMemory, token.word.Bounded :=
  terminal_bounds_of_rules hp accepted clocks initial (write_rules_of_sources sources)

/-- V2 readonly ports copy their read; actual destination writes are bounded
    by native result queries and the zero flag recovered from decoder membership. -/
theorem row_write_source {p : Nat} [Fact p.Prime] (row : Row p)
    (constraints : FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment)
      (row.constraints ()))
    (flag : row.assignment row.decoderColumns.rdIsZero = 0 ∨
      row.assignment row.decoderColumns.rdIsZero = 1) : RowWriteSources row := by
  cases row with
  | mk family w =>
    cases family
    intro port member
    change port ∈ AddSub.importedConstraintsMemoryPorts at member
    simp [AddSub.importedConstraintsMemoryPorts] at member
    rcases member with rfl | rfl | rfl
    · exact Or.inr ⟨_, by
        change _ ∈ AddSub.importedConstraintsMemoryPorts
        simp [AddSub.importedConstraintsMemoryPorts], rfl, le_rfl⟩
    · exact Or.inr ⟨_, by
        change _ ∈ AddSub.importedConstraintsMemoryPorts
        simp [AddSub.importedConstraintsMemoryPorts], rfl, le_rfl⟩
    · left
      simpa [write_word, Word.Bounded] using AddSub.Proofs.written_limb_bounds constraints flag

theorem decoded_write_sources {p : Nat} [Fact p.Prime] (hp : 256 < p)
    {trace : Data p} {setup : DecoderSetup}
    (accepted : Accepted trace) (decoded : Decoded trace setup) : WriteSources trace := by
  intro row member
  exact row_write_source row (accepted.constraints row member)
    (decoded_zero_flag hp accepted decoded row member)

theorem image_value_bounds {p : Nat} [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {trace : Data p} {setup : DecoderSetup}
    {before : Reference.RiscV.Sail.State} {cells : List Cell}
    (inputs : ImageBoundary trace before cells) (accepted : Accepted trace)
    (decoded : Decoded trace setup) :
    (∀ row ∈ trace.rows, ∀ port ∈ row.ports, (readToken row.assignment port).word.Bounded) ∧
    (∀ row ∈ trace.rows, ∀ port ∈ row.ports,
      (writeToken row.columns row.assignment port).word.Bounded) ∧
    (∀ token ∈ trace.terminalMemory, token.word.Bounded) := by
  have large : 256 < p := by dsimp [timestampBase] at hp; omega
  have clocks := image_clock_boundary (by omega) inputs
  have seeds := image_bounds inputs.image
  have sources := decoded_write_sources large accepted decoded
  exact ⟨read_bounds_of_sources hp accepted clocks seeds sources,
    write_bounds_of_sources hp accepted clocks seeds sources,
    terminal_bounds_of_sources hp accepted clocks seeds sources⟩

end Airbender.Trace.Proofs
