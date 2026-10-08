import Airbender.Review.Trace.Values
import Airbender.Proofs.Trace.MemoryOrigins
import Airbender.Proofs.AddSub
import Airbender.Proofs.WordMemory

namespace Airbender.Trace.Proofs
open Arithmetic

theorem read_word (w : Nat → ZMod p) (port : MemoryPort) :
    (readToken w port).word = ⟨(w port.readColumns[0]).val, (w port.readColumns[1]).val⟩ := by
  simp [readToken, MemoryToken.word, MemoryPort.readCode, pairCode]

theorem write_word (columns : TraceColumns) (w : Nat → ZMod p) (port : MemoryPort) :
    (writeToken columns w port).word =
      ⟨(w (port.writeColumns.getD port.readColumns)[0]).val,
        (w (port.writeColumns.getD port.readColumns)[1]).val⟩ := by
  simp [writeToken, MemoryToken.word, MemoryPort.writeCode, pairCode]

/-- A write either has locally checked bounds, or copies a read no later than
    itself. This includes timestamp-refresh writes on readonly ports. -/
theorem write_source [Fact p.Prime] {trace : Data p}
    (accepted : Accepted trace) (values : ValueBoundary trace)
    (row : Row p) (member : row ∈ trace.rows) (port : MemoryPort) (portMember : port ∈ row.ports) :
    (writeToken row.columns row.assignment port).word.Bounded ∨
      ∃ source ∈ row.ports,
        (writeToken row.columns row.assignment port).value = (readToken row.assignment source).value ∧
        (source.event row.columns row.assignment).1 ≤ (port.event row.columns row.assignment).1 := by
  have constraints := accepted.constraints row member
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
        (List.sublist_append_left (WordMemory.importedConstraints trace.rom)
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
          have copied := WordMemory.Proofs.ram_data values.disabledROM store core selected ram
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
          have ranges := values.rom _ query
          simpa [write_word, Word.Bounded] using ranges

/-- Family proofs establish this local rule from the imported equations:
    each write is bounded or copies a no-later read. -/
def WriteSources {Kind : Type} [CircuitLayout Kind] [Fact p.Prime]
    (trace : Data p Kind) : Prop :=
  ∀ row ∈ trace.rows, ∀ port ∈ row.ports,
    (writeToken row.columns row.assignment port).word.Bounded ∨
      ∃ source ∈ row.ports,
        (writeToken row.columns row.assignment port).value = (readToken row.assignment source).value ∧
        (source.event row.columns row.assignment).1 ≤ (port.event row.columns row.assignment).1

/-- Shared induction propagates the public seed bounds through native matching.
    The family-specific write rule is proved separately, not an operand premise. -/
theorem read_bounds_of_sources {Kind : Type} [CircuitLayout Kind] [Fact p.Prime]
    [ClockLaws Kind p] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : Data p Kind}
    (accepted : Accepted trace) (clocks : ClockBoundary trace)
    (initial : ∀ token ∈ trace.initialMemory, token.word.Bounded) (sources : WriteSources trace) :
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
        rcases sources writer writerMember source sourceMember with bound | copied
        · exact same ▸ bound
        · obtain ⟨read, readMember, copied, order⟩ := copied
          have before : (read.event writer.columns writer.assignment).1 < time := by omega
          have previous := ih _ before writer writerMember read readMember rfl
          unfold MemoryToken.word at previous ⊢
          rw [← congrArg MemoryToken.value same, copied]
          exact previous
  intro row member port portMember
  exact bounded _ row member port portMember rfl

theorem write_bounds_of_sources {Kind : Type} [CircuitLayout Kind] [Fact p.Prime]
    [ClockLaws Kind p] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : Data p Kind}
    (accepted : Accepted trace) (clocks : ClockBoundary trace)
    (initial : ∀ token ∈ trace.initialMemory, token.word.Bounded) (sources : WriteSources trace) :
    ∀ row ∈ trace.rows, ∀ port ∈ row.ports, (writeToken row.columns row.assignment port).word.Bounded := by
  intro row member port portMember
  rcases sources row member port portMember with bound | copied
  · exact bound
  · obtain ⟨read, readMember, copied, _⟩ := copied
    have previous := read_bounds_of_sources hp inverse accepted clocks initial sources row member read readMember
    simpa only [MemoryToken.word, copied] using previous

theorem terminal_bounds_of_sources {Kind : Type} [CircuitLayout Kind] [Fact p.Prime]
    [ClockLaws Kind p] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : Data p Kind}
    (accepted : Accepted trace) (clocks : ClockBoundary trace)
    (initial : ∀ token ∈ trace.initialMemory, token.word.Bounded) (sources : WriteSources trace) :
    ∀ token ∈ trace.terminalMemory, token.word.Bounded := by
  intro token member
  have matched := accepted.memory.mem_iff.mpr (List.mem_append_left _ member)
  rcases List.mem_append.mp matched with seed | written
  · exact initial _ seed
  · obtain ⟨row, rowMember, tokenMember⟩ := List.mem_flatMap.mp written
    obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp tokenMember
    exact write_bounds_of_sources hp inverse accepted clocks initial sources row rowMember port
      (by simpa using portMember)

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
