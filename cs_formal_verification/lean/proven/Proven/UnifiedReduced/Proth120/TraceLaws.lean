module
public import Human.Trace.UnifiedReduced.Proth120Trace
public import Proven.UnifiedReduced.Proth120.Clocks
public import Proven.Final.Circuits.UnifiedReduced.Proth120Clock
public import Proven.UnifiedReduced
public import Proven.Trace.RVValues
public import Proven.UnifiedReduced.Values

@[expose] public section
namespace Airbender.UnifiedReduced.Proth120
open Trace Trace.Proofs Arithmetic
instance : ClockLawsFor Kind proth120Modulus timeInverse where
  finalBound setup row h := final_clock_bound (Verification.holds_of_sublist h
    (List.sublist_append_right (importedConstraints setup) importedConstraintsTimestampLookups))
  advance _ _ _ _ h initial := clock_advance _ _ h initial
  portsClocks _ := by simp [Row.ports, Row.columns, CircuitLayout.ports, CircuitLayout.columns,
    importedConstraintsMemoryPorts, importedConstraintsTraceColumns]
  offsets _ := rfl
  effects _ _ _ _ h inputs := clock_accesses h inputs

/-- The two reads are refreshed, and both limbs of the destination write are range-checked. -/
private theorem write_sources {trace : WrapTrace} (accepted : Accepted trace) : WriteSources trace := by
  intro row member port present
  have core := Standard.holds (Verification.holds_of_sublist (accepted.constraints row member)
    (List.sublist_append_left (importedConstraints trace.rom) importedConstraintsTimestampLookups))
  simp [Row.ports, CircuitLayout.ports, importedConstraintsMemoryPorts] at present
  rcases present with rfl | rfl | rfl
  · exact Or.inr ⟨_, by simp [Row.ports, CircuitLayout.ports, importedConstraintsMemoryPorts], rfl, le_rfl⟩
  · exact Or.inr ⟨_, by simp [Row.ports, CircuitLayout.ports, importedConstraintsMemoryPorts], rfl, le_rfl⟩
  · left
    simpa [write_word, Word.Bounded] using UnifiedReduced.Standard.Proofs.destination_bounds (profile := .proth120) core

theorem read_bounds {trace : WrapTrace} {initial cells} (inputs : TraceInputs trace initial cells)
    (accepted : Accepted trace) (row : Row proth120Modulus Kind) (member : row ∈ trace.rows) :
    (wordAt row.assignment 36).Bounded ∧ (wordAt row.assignment 42).Bounded ∧
      (wordAt row.assignment 48).Bounded := by
  have bounds := read_bounds_of_rules (by decide : 2 * timestampBase + 4 < proth120Modulus) time_inverse
    accepted inputs.clocks (RVValues.rv_image_bounds inputs.image) (write_rules_of_sources (write_sources accepted))
  have h (i : Fin 3) := bounds row member importedConstraintsMemoryPorts[i]
    (by fin_cases i <;> simp [Row.ports, CircuitLayout.ports, importedConstraintsMemoryPorts])
  refine ⟨?_, ?_, ?_⟩ <;> first
    | simpa [readToken, MemoryToken.word, MemoryPort.readCode, WordColumns.code, pairCode,
        importedConstraintsMemoryPorts, wordAt] using h 0
    | simpa [readToken, MemoryToken.word, MemoryPort.readCode, WordColumns.code, pairCode,
        importedConstraintsMemoryPorts, wordAt] using h 1
    | simpa [readToken, MemoryToken.word, MemoryPort.readCode, WordColumns.code, pairCode,
        importedConstraintsMemoryPorts, wordAt] using h 2

end Airbender.UnifiedReduced.Proth120
