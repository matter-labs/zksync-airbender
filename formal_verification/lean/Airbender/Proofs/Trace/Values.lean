import Airbender.Review.Helpers.Memory.Values
import Airbender.Proofs.Trace.MemoryOrigins
import Airbender.Proofs.AddSub
import Airbender.Proofs.WordMemory

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

/-- A write either has locally checked bounds, or copies a read no later than
    itself. This includes timestamp-refresh writes on readonly ports. -/
theorem row_write_source [Fact p.Prime] (row : Row p)
    (setup : Table (ZMod p) (fields 9))
    (constraints : FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment)
      (row.constraints setup))
    (disabledROM : ∀ query, setup.Contains #[] query → query[8] = 0 → query[1] = 0 ∧ query[2] = 0)
    (rom : ∀ query, setup.Contains #[] query → query[1].val < limbBase ∧ query[2].val < limbBase)
    (port : MemoryPort) (portMember : port ∈ row.ports) :
    (writeToken row.columns row.assignment port).word.Bounded ∨
      ∃ source ∈ row.ports,
        (writeToken row.columns row.assignment port).value = (readToken row.assignment source).value ∧
        (source.event row.columns row.assignment).1 ≤ (port.event row.columns row.assignment).1 := by
  cases row with
  | mk family w =>
    cases family with
    | addSub =>
      have core := Verification.holds_of_sublist constraints
        (List.sublist_append_left AddSub.importedConstraints AddSub.importedConstraintsTimestampLookups)
      simp [Row.ports, AddSub.importedConstraintsMemoryPorts] at portMember
      rcases portMember with rfl | rfl | rfl
      · exact Or.inr ⟨_, by simp [Row.ports, AddSub.importedConstraintsMemoryPorts], rfl, le_rfl⟩
      · exact Or.inr ⟨_, by simp [Row.ports, AddSub.importedConstraintsMemoryPorts], rfl, le_rfl⟩
      · left
        simpa [write_word, Word.Bounded] using AddSub.Proofs.written_limb_bounds core
    | wordMemory =>
      have core := Verification.holds_of_sublist constraints
        (List.sublist_append_left (WordMemory.importedConstraints setup)
          WordMemory.importedConstraintsTimestampLookups)
      simp [Row.ports, WordMemory.importedConstraintsMemoryPorts] at portMember
      rcases portMember with rfl | rfl | rfl
      · exact Or.inr ⟨_, by simp [Row.ports, WordMemory.importedConstraintsMemoryPorts], rfl, le_rfl⟩
      · exact Or.inr ⟨_, by simp [Row.ports, WordMemory.importedConstraintsMemoryPorts], rfl, le_rfl⟩
      · have selector : w 10 = 0 ∨ w 10 = 1 := by
          simpa using WordMemory.Proofs.local_flags core 1
        have rom : w 35 = 0 ∨ w 35 = 1 := by
          simpa using WordMemory.Proofs.local_flags core 2
        obtain ⟨store, selected⟩ : ∃ store : Bool, w 10 = if store then 1 else 0 := by
          rcases selector with hs | hs
          · exact ⟨false, hs⟩
          · exact ⟨true, hs⟩
        rcases rom with ram | inROM
        · right
          have copied := WordMemory.Proofs.ram_data disabledROM store core selected ram
          change w 31 = w 23 ∧ w 32 = w 24 at copied
          refine ⟨WordMemory.importedConstraintsMemoryPorts[1],
            by simp [Row.ports, WordMemory.importedConstraintsMemoryPorts], ?_, ?_⟩
          · simp [writeToken, readToken, MemoryPort.writeCode, MemoryPort.readCode, pairCode,
              WordMemory.importedConstraintsMemoryPorts, copied.1, copied.2]
          · change (decodeTimestamp w _).value + 1 ≤ (decodeTimestamp w _).value + 2
            omega
        · left
          have query := WordMemory.Proofs.data_lookup store core selected
          simp only [inROM, one_mul, sub_self, zero_mul, sub_zero] at query
          have ranges := rom _ query
          simpa [write_word, Word.Bounded] using ranges

theorem write_source [Fact p.Prime] {trace : Data p}
    (accepted : Accepted trace) (values : ValueBoundary trace)
    (row : Row p) (member : row ∈ trace.rows) (port : MemoryPort) (portMember : port ∈ row.ports) :
    (writeToken row.columns row.assignment port).word.Bounded ∨
      ∃ source ∈ row.ports,
        (writeToken row.columns row.assignment port).value = (readToken row.assignment source).value ∧
        (source.event row.columns row.assignment).1 ≤ (port.event row.columns row.assignment).1 :=
  row_write_source row trace.rom (accepted.constraints row member) values.disabledROM values.rom port portMember

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
    (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : Data p Kind}
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
      rcases earlier_write hp inverse accepted clocks row member port portMember with seed | prior
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
    (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : Data p Kind}
    (accepted : Accepted trace) (clocks : ClockBoundary trace)
    (initial : ∀ token ∈ trace.initialMemory, token.word.Bounded)
    (rules : WriteBoundsFromReads trace) :
    ∀ row ∈ trace.rows, ∀ port ∈ row.ports,
      (writeToken row.columns row.assignment port).word.Bounded := by
  intro row member port present
  exact rules row member port present (fun read readMember _ =>
    read_bounds_of_rules hp inverse accepted clocks initial rules row member read readMember)

theorem terminal_bounds_of_rules {Kind : Type} [CircuitLayout Kind] [Fact p.Prime]
    [ClockLaws Kind p] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : Data p Kind}
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
    exact write_bounds_of_rules hp inverse accepted clocks initial rules row rowMember port
      (by simpa using portMember)

-- Compatibility with existing family proofs; the induction above is shared.
theorem read_bounds_of_sources {Kind : Type} [CircuitLayout Kind] [Fact p.Prime]
    [ClockLaws Kind p] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : Data p Kind}
    (accepted : Accepted trace) (clocks : ClockBoundary trace)
    (initial : ∀ token ∈ trace.initialMemory, token.word.Bounded) (sources : WriteSources trace) :
    ∀ row ∈ trace.rows, ∀ port ∈ row.ports, (readToken row.assignment port).word.Bounded :=
  read_bounds_of_rules hp inverse accepted clocks initial (write_rules_of_sources sources)

theorem write_bounds_of_sources {Kind : Type} [CircuitLayout Kind] [Fact p.Prime]
    [ClockLaws Kind p] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : Data p Kind}
    (accepted : Accepted trace) (clocks : ClockBoundary trace)
    (initial : ∀ token ∈ trace.initialMemory, token.word.Bounded) (sources : WriteSources trace) :
    ∀ row ∈ trace.rows, ∀ port ∈ row.ports, (writeToken row.columns row.assignment port).word.Bounded :=
  write_bounds_of_rules hp inverse accepted clocks initial (write_rules_of_sources sources)

theorem terminal_bounds_of_sources {Kind : Type} [CircuitLayout Kind] [Fact p.Prime]
    [ClockLaws Kind p] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : Data p Kind}
    (accepted : Accepted trace) (clocks : ClockBoundary trace)
    (initial : ∀ token ∈ trace.initialMemory, token.word.Bounded) (sources : WriteSources trace) :
    ∀ token ∈ trace.terminalMemory, token.word.Bounded :=
  terminal_bounds_of_rules hp inverse accepted clocks initial (write_rules_of_sources sources)

theorem read_bounds [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : Data p}
    (accepted : Accepted trace) (clocks : ClockBoundary trace) (values : ValueBoundary trace) :
    ∀ row ∈ trace.rows, ∀ port ∈ row.ports, (readToken row.assignment port).word.Bounded :=
  read_bounds_of_sources hp inverse accepted clocks values.initial (write_source accepted values)

theorem write_bounds [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : Data p}
    (accepted : Accepted trace) (clocks : ClockBoundary trace) (values : ValueBoundary trace) :
    ∀ row ∈ trace.rows, ∀ port ∈ row.ports, (writeToken row.columns row.assignment port).word.Bounded :=
  write_bounds_of_sources hp inverse accepted clocks values.initial (write_source accepted values)

theorem terminal_bounds [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : Data p}
    (accepted : Accepted trace) (clocks : ClockBoundary trace) (values : ValueBoundary trace) :
    ∀ token ∈ trace.terminalMemory, token.word.Bounded :=
  terminal_bounds_of_sources hp inverse accepted clocks values.initial (write_source accepted values)

end Airbender.Trace.Proofs
