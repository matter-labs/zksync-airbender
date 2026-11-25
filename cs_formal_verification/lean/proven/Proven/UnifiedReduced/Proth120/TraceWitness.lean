module
public import Human.Trace.UnifiedReduced.Proth120Trace
public import Proven.UnifiedReduced.Proth120.RowWitness
public import Proven.Constraints

@[expose] public section
namespace Airbender.UnifiedReduced.Proth120.Witness
open Trace Verification

abbrev row : Row proth120Modulus Kind := ⟨.machine, assignment .fma⟩
noncomputable def trace : WrapTrace where
  rows := [row]
  rom := tableWith (ROM.wordsRV initial)
  initial := row.start
  terminal := row.finish
  initialMemory := row.reads
  terminalMemory := row.writes

theorem trace_inputs : TraceInputs trace initial cells where
  image := by kernel_rfl
  distinct := by decide
  aligned := fma_inputs.aligned
  pc := by kernel_rfl
  clocks := {
    initial := ⟨by decide, by decide⟩
    aligned := by decide
    memory := by
      intro token h
      change token ∈ [_ , _, _] at h
      rcases List.mem_cons.mp h with rfl | h
      · exact ⟨by decide, by decide⟩
      rcases List.mem_cons.mp h with rfl | h
      · exact ⟨by decide, by decide⟩
      obtain rfl := List.mem_singleton.mp h
      exact ⟨by decide, by decide⟩ }
  setup := rfl
  stream := by
    intro r hr h
    obtain rfl := List.mem_singleton.mp hr
    exact False.elim ((by decide +kernel : isRead row ≠ true) h)
  decoded := by
    intro r member
    obtain rfl := List.mem_singleton.mp member
    exact ⟨fma_inputs.fetch.1, fma_inputs.fetch.2, Or.inl ⟨by decide +kernel, fma_inputs.decoded⟩⟩

theorem trace_accepted : Accepted trace where
  constraints := by
    intro r member
    obtain rfl := List.mem_singleton.mp member
    exact Verification.holds_append fma_inputs.constraints (clocks .fma)
  active := by intro r member; obtain rfl := List.mem_singleton.mp member; exact fma_inputs.active
  states := List.Perm.swap _ _ _
  memory := by simpa [trace] using List.perm_append_comm (l₁ := row.reads) (l₂ := row.writes)

end Airbender.UnifiedReduced.Proth120.Witness
