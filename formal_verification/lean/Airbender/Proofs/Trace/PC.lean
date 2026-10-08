import Airbender.Proofs.Trace.InitialImage
import Airbender.Proofs.AddSub.PC
import Airbender.Proofs.WordMemory

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

/-- Every input and terminal PC matches the initial state or a locally ranged
    output. Native matching therefore removes every per-row initial-PC bound. -/
theorem trace_pc_bounds [Fact p.Prime] {trace : Data p} (accepted : Accepted trace)
    (initial : trace.initial.word.Bounded) :
    (∀ row ∈ trace.rows, row.start.word.Bounded ∧ row.finish.word.Bounded) ∧
      trace.terminal.word.Bounded := by
  have outputs : ∀ state ∈ trace.rows.map Row.finish, state.word.Bounded := by
    intro state member
    obtain ⟨row, rowMember, rfl⟩ := List.mem_map.mp member
    exact final_pc_bound row trace.rom (accepted.constraints row rowMember)
  have incoming : ∀ state ∈ trace.terminal :: trace.rows.map Row.start, state.word.Bounded := by
    intro state member
    have matched := accepted.states.mem_iff.mpr member
    rcases List.mem_cons.mp matched with rfl | finished
    · exact initial
    · exact outputs state finished
  refine ⟨?_, incoming _ List.mem_cons_self⟩
  intro row member
  exact ⟨incoming _ (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨row, member, rfl⟩)),
    final_pc_bound row trace.rom (accepted.constraints row member)⟩

end Airbender.Trace.Proofs
