import Slop.Trace.InitialImage
import Slop.AddSub.PC
import Slop.WordMemory

namespace Airbender.Trace.Proofs
open Arithmetic

theorem final_pc_bound [Fact p.Prime] (row : Row p) (rom : Table (ZMod p) (fields 9))
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment)
      (row.constraints rom)) : row.finish.word.Bounded := by
  cases row with
  | mk family w =>
    cases family with
    | addSub =>
      have core := Verification.holds_of_sublist h
        (List.sublist_append_left AddSub.importedConstraints AddSub.importedConstraintsTimestampLookups)
      have bounds := AddSub.Proofs.pc_bounds core
        (initial := ⟨(w 0).val, (w 1).val⟩) (final := ⟨(w 19).val, (w 20).val⟩)
        ⟨(ZMod.natCast_zmod_val _).symm, (ZMod.natCast_zmod_val _).symm, rfl, rfl⟩
      exact bounds
    | wordMemory =>
      have core := Verification.holds_of_sublist h
        (List.sublist_append_left (WordMemory.importedConstraints rom) WordMemory.importedConstraintsTimestampLookups)
      exact (WordMemory.Proofs.local_ranges core).2

/-- Decoder-bound incoming PCs constrain every outgoing PC except an external
    terminal state. A canonical endpoint is a separate, explicit boundary. -/
theorem outgoing_pc_bounds {Kind : Type} [CircuitLayout Kind] [Fact p.Prime]
    {trace : Data p Kind} (accepted : Accepted trace)
    (incoming : ∀ row ∈ trace.rows, row.start.word.Bounded)
    (terminal : trace.terminal.word.Bounded) :
    ∀ row ∈ trace.rows, row.finish.word.Bounded := by
  intro row member
  have matched := accepted.states.mem_iff.mp
    (List.mem_cons_of_mem trace.initial (List.mem_map.mpr ⟨row, member, rfl⟩))
  rcases List.mem_cons.mp matched with final | other
  · exact final ▸ terminal
  · obtain ⟨next, present, same⟩ := List.mem_map.mp other
    exact same ▸ incoming next present

/-- Native matching transports a state property from the public initial state
    and the locally checked outputs to all incoming states and termination. -/
theorem matched_incoming_property {Kind : Type} [CircuitLayout Kind] [Fact p.Prime]
    {trace : Data p Kind} (accepted : Accepted trace) (property : PCState.State p → Prop)
    (initial : property trace.initial)
    (outputs : ∀ row ∈ trace.rows, property row.finish) :
    ∀ state ∈ trace.terminal :: trace.rows.map Row.start, property state := by
  intro state member
  have matched := accepted.states.mem_iff.mpr member
  rcases List.mem_cons.mp matched with same | finished
  · exact same ▸ initial
  · obtain ⟨row, present, same⟩ := List.mem_map.mp finished
    exact same ▸ outputs row present

/-- Locally ranged outputs remove every per-row initial-PC bound. -/
theorem trace_pc_bounds [Fact p.Prime] {trace : Data p} (accepted : Accepted trace)
    (initial : trace.initial.word.Bounded) :
    (∀ row ∈ trace.rows, row.start.word.Bounded ∧ row.finish.word.Bounded) ∧
      trace.terminal.word.Bounded := by
  have incoming := matched_incoming_property accepted (fun state => state.word.Bounded) initial
    (fun row member => final_pc_bound row trace.rom (accepted.constraints row member))
  refine ⟨?_, incoming _ List.mem_cons_self⟩
  intro row member
  exact ⟨incoming _ (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨row, member, rfl⟩)),
    final_pc_bound row trace.rom (accepted.constraints row member)⟩

/-- Global native PC matching supplies each input bound; the imported equations
    then enforce the common four-byte increment for both selected families. -/
theorem row_pc_successor [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : Data p}
    (accepted : Accepted trace) (initial : trace.initial.word.Bounded)
    {row : Row p} (member : row ∈ trace.rows) :
    row.finish.word.toBitVec = row.start.word.toBitVec + 4 := by
  have bound := (trace_pc_bounds accepted initial).1 row member
  have constraints := accepted.constraints row member
  have addressInverse : (-30720 : ZMod p) * 65536 = 1 := by
    calc
      (-30720 : ZMod p) * 65536 = (-3840 : ZMod p) * 524288 := by ring
      _ = 1 := inverse
  cases row with
  | mk family w =>
    cases family with
    | addSub =>
      have core := Verification.holds_of_sublist constraints
        (List.sublist_append_left AddSub.importedConstraints AddSub.importedConstraintsTimestampLookups)
      exact (AddSub.Proofs.pc_successor (by dsimp [timestampBase] at hp; omega)
        addressInverse core
        ⟨(ZMod.natCast_zmod_val _).symm, (ZMod.natCast_zmod_val _).symm, rfl, rfl⟩ bound.1).2.2
    | wordMemory =>
      have core := Verification.holds_of_sublist constraints
        (List.sublist_append_left (WordMemory.importedConstraints trace.rom)
          WordMemory.importedConstraintsTimestampLookups)
      exact (WordMemory.Proofs.pc_successor (by dsimp [timestampBase] at hp; omega)
        addressInverse core
        ⟨(ZMod.natCast_zmod_val _).symm, (ZMod.natCast_zmod_val _).symm, rfl, rfl⟩ bound.1).2.2

end Airbender.Trace.Proofs
