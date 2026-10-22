import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Review.Helpers.Core.SerializedInverse
import Airbender.Proofs.UnifiedReduced.Trace
import Airbender.Proofs.UnifiedReduced
import Airbender.Proofs.Trace.Values
import Airbender.Proofs.Trace.InitialImage
import Airbender.Proofs.Trace.MemoryHistory

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

theorem value_bounds {p : Nat} [Fact p.Prime]
    (hp : FieldCapacity.ClockNoWrap p timestampBase) (inverse : SerializedInverse.Clock p)
    {trace : UnifiedTrace p} (accepted : Accepted trace) (clocks : ClockBoundary trace)
    {before : Reference.RiscV.Sail.State} {cells : List Cell}
    (image : initialImage before cells = some trace.initialMemory) :
    (∀ row ∈ trace.rows, ∀ port ∈ row.ports, (readToken row.assignment port).word.Bounded) ∧
    (∀ row ∈ trace.rows, ∀ port ∈ row.ports,
      (writeToken row.columns row.assignment port).word.Bounded) ∧
    (∀ token ∈ trace.terminalMemory, token.word.Bounded) := by
  have sources : WriteSources trace :=
    fun row present => row_write_sources row (accepted.constraints row present)
  have rules := write_rules_of_sources sources
  have seed := image_bounds image
  exact ⟨read_bounds_of_rules hp inverse accepted clocks seed rules,
    write_bounds_of_rules hp inverse accepted clocks seed rules,
    terminal_bounds_of_rules hp inverse accepted clocks seed rules⟩

theorem memory_history {p : Nat} [Fact p.Prime]
    (hp : FieldCapacity.ClockNoWrap p timestampBase) (inverse : SerializedInverse.Clock p)
    {trace : UnifiedTrace p} (accepted : Accepted trace) (clocks : ClockBoundary trace)
    {before : Reference.RiscV.Sail.State} {cells : List Cell}
    (image : initialImage before cells = some trace.initialMemory) (distinct : cells.Nodup) :
    ∃ history, MemoryHistory trace history :=
  native_memory_history hp inverse accepted clocks (image_unique image distinct)

end Airbender.UnifiedReduced.Proofs
