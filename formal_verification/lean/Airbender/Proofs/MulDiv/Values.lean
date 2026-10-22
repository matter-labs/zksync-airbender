import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Review.Helpers.Core.SerializedInverse
import Airbender.Proofs.MulDiv.Trace
import Airbender.Proofs.Trace.Values

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

/-- Every operand, write and terminal register has bounded limbs, derived
    from the public Sail seed and latest-write/read consistency. -/
theorem native_value_bounds {p : Nat} [Fact p.Prime]
    (hp : FieldCapacity.ClockNoWrap p timestampBase) (inverse : SerializedInverse.Clock p)
    {trace : NativeTrace p} (accepted : Accepted trace) (clocks : ClockBoundary trace)
    {before : Reference.RiscV.Sail.State} {cells : List Cell}
    (image : initialImage before cells = some trace.initialMemory) :
    (∀ row ∈ trace.rows, ∀ port ∈ row.ports, (readToken row.assignment port).word.Bounded) ∧
      (∀ row ∈ trace.rows, ∀ port ∈ row.ports,
        (writeToken row.columns row.assignment port).word.Bounded) ∧
      (∀ token ∈ trace.terminalMemory, token.word.Bounded) := by
  have sources := write_sources accepted
  have seed := Trace.Proofs.image_bounds image
  exact ⟨Trace.Proofs.read_bounds_of_sources hp inverse accepted clocks seed sources,
    Trace.Proofs.write_bounds_of_sources hp inverse accepted clocks seed sources,
    Trace.Proofs.terminal_bounds_of_sources hp inverse accepted clocks seed sources⟩

end Airbender.MulDiv.Proofs
