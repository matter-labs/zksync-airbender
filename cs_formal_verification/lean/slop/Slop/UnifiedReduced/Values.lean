module
public import Slop.UnifiedReduced.Trace
public import Slop.UnifiedReduced
public import Slop.Trace.Values
public import Slop.Trace.InitialImage
public import Slop.Trace.MemoryHistory

@[expose] public section

namespace Airbender.UnifiedReduced.Proofs
open Arithmetic Trace Trace.Proofs

theorem row_write_sources {p : Nat} [Fact p.Prime]
    {setup : Table (ZMod p) (fields 10)} (row : Row p UnifiedFamily)
    (constraints : FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment)
      (row.constraints setup)) : RowWriteSources row := by
  cases row with
  | mk family w =>
    have core := Verification.holds_of_sublist constraints
      (List.sublist_append_left (importedConstraints setup) importedConstraintsTimestampLookups)
    intro port present
    simp [Row.ports, CircuitLayout.ports, importedConstraintsMemoryPorts] at present
    rcases present with rfl | rfl | rfl
    · exact Or.inr ⟨_, by simp [Row.ports, CircuitLayout.ports, importedConstraintsMemoryPorts],
        rfl, le_rfl⟩
    · exact Or.inr ⟨_, by simp [Row.ports, CircuitLayout.ports, importedConstraintsMemoryPorts],
        rfl, le_rfl⟩
    · left
      simpa [write_word, Word.Bounded] using destination_bounds core

end Airbender.UnifiedReduced.Proofs
