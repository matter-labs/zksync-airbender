module
public import Human.Trace.Machine.Model
public import Proven.Trace.Machine.Fetch

@[expose] public section
namespace Airbender.Trace.Machine.Proofs
open Arithmetic
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-- Public native queries and the typed terminal boundary bound every outgoing row PC. -/
theorem machine_finish_bounds {Kind : Type} [CircuitLayout Kind] {trace : Data babyBearModulus Kind}
    (states : (trace.initial :: trace.rows.map Row.finish).Perm (trace.terminal :: trace.rows.map Row.start))
    (queries : ∀ row ∈ trace.rows, ∃ entry : RVMachineProgramEntry,
      row.decoderQuery = (entry.data.row entry.pc).map (fun value : Nat => (value : ZMod babyBearModulus)))
    (terminal : trace.terminal.word.Bounded) : ∀ row ∈ trace.rows, row.finish.word.Bounded := by
  have starts : ∀ row ∈ trace.rows, row.start.word.Bounded := by
    intro row member
    obtain ⟨entry, query⟩ := queries row member
    have word : row.start.word = Word.ofBitVec entry.pc := machine_native_query_pc_word (by decide) query
    rw [word]
    exact Word.ofBitVec_bound _
  intro row member
  have endpoint := states.mem_iff.mp (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨row, member, rfl⟩))
  rcases List.mem_cons.mp endpoint with same | incoming
  · rw [same]
    exact terminal
  · obtain ⟨source, present, same⟩ := List.mem_map.mp incoming
    rw [← same]
    exact starts source present

end Airbender.Trace.Machine.Proofs
