module
public import Slop.MulDiv.Trace
public import Slop.Trace.Values
public import Slop.Defs.Helpers.Memory.Ports

@[expose] public section

namespace Airbender.MulDiv.Proofs
open Arithmetic Trace

/-- Readonly ports copy their reads; imported queries bound destination
    writes. This is the shared history induction's only family-specific input. -/
theorem row_write_sources {p : Nat} [Fact p.Prime] (row : Row p TraceKind)
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment) importedConstraints) :
    Trace.Proofs.RowWriteSources row := by
  intro port present
  simp [Row.ports, importedConstraintsMemoryPorts] at present
  rcases present with rfl | rfl | rfl
  · exact Or.inr ⟨_, by simp [Row.ports, importedConstraintsMemoryPorts], rfl, le_rfl⟩
  · exact Or.inr ⟨_, by simp [Row.ports, importedConstraintsMemoryPorts], rfl, le_rfl⟩
  · left
    have ranges := local_ranges h
    simpa [Trace.Proofs.write_word, importedConstraintsMemoryPorts] using
      (show (⟨(row.assignment 28).val, (row.assignment 29).val⟩ : Word).Bounded from
        ⟨ranges ⟨0, by decide⟩, ranges ⟨1, by decide⟩⟩)

theorem write_sources {p : Nat} [Fact p.Prime]
    {trace : NativeTrace p} (accepted : Accepted trace) : Trace.Proofs.WriteSources trace := by
  intro row member
  exact row_write_sources row (Verification.holds_of_sublist (accepted.constraints row member)
    (List.sublist_append_left importedConstraints importedConstraintsTimestampLookups))

end Airbender.MulDiv.Proofs
