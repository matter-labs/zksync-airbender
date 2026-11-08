module
public import Slop.Trace.InitialImage

@[expose] public section

namespace Airbender.Trace.Proofs
open Arithmetic

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

end Airbender.Trace.Proofs
