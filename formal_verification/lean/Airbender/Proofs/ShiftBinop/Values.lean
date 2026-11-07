import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Review.Helpers.Core.SerializedInverse
import Airbender.Proofs.ShiftBinop.Trace
import Airbender.Proofs.ShiftBinop.Ports
import Airbender.Proofs.Trace.Values

namespace Airbender.ShiftBinop.Proofs
open Arithmetic Trace

/-- Native writes are bounded before read transport. Actual public decoding
    selects the tag; imported lookups and assembly bound the result. -/
theorem row_write_sources {p : Nat} [Fact p.Prime] (hp : FieldCapacity.NoWrap p 262144)
    (row : Row p TraceKind)
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment) importedConstraints)
    {before : Reference.RiscV.Sail.State} (fetch : Fetched row.assignment before) :
    Trace.Proofs.RowWriteSources row := by
  intro port present
  simp [Row.ports, importedConstraintsMemoryPorts] at present
  rcases present with rfl | rfl | rfl
  · exact Or.inr ⟨_, by simp [Row.ports, importedConstraintsMemoryPorts], rfl, le_rfl⟩
  · exact Or.inr ⟨_, by simp [Row.ports, importedConstraintsMemoryPorts], rfl, le_rfl⟩
  · left
    obtain ⟨entry, source, query, _⟩ := fetch
    have flags := decoder_selectors (by dsimp [limbBase]; omega) h
      (decoder_field_bounds source.fields).2.1 query
    have tag := congrArg (fun q : Vector (ZMod p) 9 => q[7]) query
    change row.assignment 10 = (entry.data.funct3 : ZMod p) at tag
    have code : (row.assignment 10).val = entry.data.funct3 := by
      have small := (decoder_field_bounds source.fields).2.2
      rw [tag, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
    have destination : (row.assignment 31).val < limbBase ∧
        (row.assignment 32).val < limbBase := by
      rcases decoder_operation_tags source.fields with ⟨mask, tags⟩ | ⟨mask, tags⟩
      · have selected : row.assignment 11 = 1 ∧ row.assignment 12 = 0 := by
          constructor
          · simpa [importedConstraintsDecoderColumns, mask, Nat.testBit] using flags 0
          · simpa [importedConstraintsDecoderColumns, mask, Nat.testBit] using flags 1
        exact shift_written_bounds hp h selected (code.symm ▸ tags)
      · have selected : row.assignment 11 = 0 ∧ row.assignment 12 = 1 := by
          constructor
          · simpa [importedConstraintsDecoderColumns, mask, Nat.testBit] using flags 0
          · simpa [importedConstraintsDecoderColumns, mask, Nat.testBit] using flags 1
        exact binary_written_bounds (by omega) h selected _ tags tag
    simpa [Trace.Proofs.write_word, importedConstraintsMemoryPorts, Word.Bounded] using destination

theorem write_sources {p : Nat} [Fact p.Prime] (hp : FieldCapacity.NoWrap p 262144)
    {trace : NativeTrace p} (accepted : Accepted trace)
    {before : Reference.RiscV.Sail.State} {addresses : List (BitVec 32)}
    {program : List ProgramEntry} (image : programImage before addresses = some program)
    (decoded : Decoded trace program) : Trace.Proofs.WriteSources trace := by
  intro row member
  have h := Verification.holds_of_sublist (accepted.constraints row member)
    (List.sublist_append_left importedConstraints importedConstraintsTimestampLookups)
  exact row_write_sources hp row h (fetched (by dsimp [limbBase]; omega) image h (decoded row member))

/-- Shared latest-write/read induction derives bounded operands, writes and
    terminal cells from public initialization, without a result premise. -/
theorem native_value_bounds {p : Nat} [Fact p.Prime]
    (hp : FieldCapacity.ClockNoWrap p timestampBase) (inverse : SerializedInverse.Clock p)
    {trace : NativeTrace p} (accepted : Accepted trace) (clocks : ClockBoundary trace)
    {before : Reference.RiscV.Sail.State} {cells : List Cell}
    (image : initialImage before cells = some trace.initialMemory)
    {addresses : List (BitVec 32)} {program : List ProgramEntry}
    (programImage : ShiftBinop.programImage before addresses = some program)
    (decoded : Decoded trace program) :
    (∀ row ∈ trace.rows, ∀ port ∈ row.ports, (readToken row.assignment port).word.Bounded) ∧
      (∀ row ∈ trace.rows, ∀ port ∈ row.ports,
        (writeToken row.columns row.assignment port).word.Bounded) ∧
      (∀ token ∈ trace.terminalMemory, token.word.Bounded) := by
  have sources := write_sources (by dsimp [timestampBase] at hp; omega)
    accepted programImage decoded
  have seed := Trace.Proofs.image_bounds image
  exact ⟨Trace.Proofs.read_bounds_of_sources hp inverse accepted clocks seed sources,
    Trace.Proofs.write_bounds_of_sources hp inverse accepted clocks seed sources,
    Trace.Proofs.terminal_bounds_of_sources hp inverse accepted clocks seed sources⟩

end Airbender.ShiftBinop.Proofs
