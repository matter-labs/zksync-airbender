module
public import Human.Trace.UnifiedReduced.Proth120Trace
public import Proven.UnifiedReduced.Proth120.CSRWitness
public import Proven.Constraints

@[expose] public section
namespace Airbender.UnifiedReduced.Proth120.CSRWitness
open Trace Verification

abbrev row : Row proth120Modulus Kind := ⟨.machine, assignment true⟩

/-- Both source ports refresh x0 consecutively. Only the first incoming and last outgoing
    token for x0 belong to the boundary. The destination port changes x3 from zero to seven. -/
noncomputable def trace : WrapTrace where
  rows := [row]
  rom := tableWith (ROM.wordsRV (initial true))
  initial := row.start
  terminal := row.finish
  initialMemory := [row.reads[0], row.reads[2]]
  terminalMemory := [row.writes[1], row.writes[2]]

theorem trace_inputs : TraceInputs trace (initial true) cells where
  image := by kernel_rfl
  distinct := by decide
  aligned := (inputs true).aligned
  pc := by kernel_rfl
  clocks := {
    initial := ⟨by decide, by decide⟩
    aligned := by decide
    memory := by
      intro token h
      rcases List.mem_cons.mp h with rfl | h
      · exact ⟨by decide, by decide⟩
      obtain rfl := List.mem_singleton.mp h
      exact ⟨by decide, by decide⟩ }
  setup := rfl
  stream := by
    intro r member _
    obtain rfl := List.mem_singleton.mp member
    kernel_rfl
  decoded := by
    intro r member
    obtain rfl := List.mem_singleton.mp member
    exact ⟨(inputs true).fetch.1, (inputs true).fetch.2, Or.inr (inputs true).decoded⟩

theorem trace_accepted : Accepted trace where
  constraints := by
    intro r member
    obtain rfl := List.mem_singleton.mp member
    exact holds_append (inputs true).constraints (clocks true)
  active := by intro r member; obtain rfl := List.mem_singleton.mp member; exact (inputs true).active
  states := List.Perm.swap _ _ _
  memory := by decide +kernel

end Airbender.UnifiedReduced.Proth120.CSRWitness
