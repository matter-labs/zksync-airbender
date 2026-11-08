import Slop.Trace.RVValues
import Slop.ShiftBinop.RVDecoder
import Slop.ShiftBinop.Ports
import Slop.ShiftBinop.Trace

/-! ShiftBinop row facts of the RV value-bounds law (`RVValuesPooled`): write sources from the RV projection
    equation. -/

namespace Airbender.ShiftBinop.Proofs
open Arithmetic Trace

/-- `row_write_sources` with the Sail `Fetched` replaced by the projection equation and the query. -/
theorem rv_row_write_sources {p : Nat} [Fact p.Prime] (hp : 262144 < p)
    (row : Row p TraceKind)
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment) importedConstraints)
    {entry : RVProgramEntry} {i : RV.Instr} (fields : rvDecoderFields i = some entry.data)
    (query : decoderQuery row.assignment = entry.query) :
    Trace.Proofs.RowWriteSources row := by
  intro port present
  simp [Row.ports, importedConstraintsMemoryPorts] at present
  rcases present with rfl | rfl | rfl
  · exact Or.inr ⟨_, by simp [Row.ports, importedConstraintsMemoryPorts], rfl, le_rfl⟩
  · exact Or.inr ⟨_, by simp [Row.ports, importedConstraintsMemoryPorts], rfl, le_rfl⟩
  · left
    have flags := rv_decoder_selectors (by dsimp [limbBase]; omega) h
      (rv_decoder_field_bounds fields).2.1 query
    have tag := congrArg (fun q : Vector (ZMod p) 9 => q[7]) query
    change row.assignment 10 = (entry.data.funct3 : ZMod p) at tag
    have code : (row.assignment 10).val = entry.data.funct3 := by
      have small := (rv_decoder_field_bounds fields).2.2
      rw [tag, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
    have destination : (row.assignment 31).val < limbBase ∧
        (row.assignment 32).val < limbBase := by
      rcases rv_decoder_operation_tags fields with ⟨mask, tags⟩ | ⟨mask, tags⟩
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

end Airbender.ShiftBinop.Proofs
