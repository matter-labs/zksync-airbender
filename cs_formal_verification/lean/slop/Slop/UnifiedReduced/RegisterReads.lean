import Slop.UnifiedReduced.History

namespace Airbender.UnifiedReduced.Proofs
open Arithmetic Reference.RiscV Reference.RiscV.Sail Reference.Sail Trace Trace.Proofs
set_option warningAsError true
set_option maxRecDepth 16384

theorem register_reads [Fact p.Prime] (hp : limbBase < p)
    {setup : Table (ZMod p) (fields 10)} {w : Nat → ZMod p} {entry : ProgramEntry}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (noRAM : w 28 = 0) (query : decoderQuery w = entry.query)
    {cells : List Cell} (epoch : Nat) {before after : State}
    (history : SailHistory cells
      (rowEvents epoch (⟨.machine, w⟩ : Row p UnifiedFamily)).reverse before after) :
    run (SailRV32.Functions.rX_bits (.Regidx entry.data.rs1)) before =
      .ok (Word.mk (w 36).val (w 37).val).toBitVec before ∧
    run (SailRV32.Functions.rX_bits (.Regidx entry.data.rs2)) before =
      .ok (Word.mk (w 42).val (w 43).val).toBitVec before := by
  have indices := native_query_indices hp query
  have low := Verification.assertion_of_holds h ⟨29, by rw [constraint_count]; decide⟩
  have high := Verification.assertion_of_holds h ⟨30, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment, noRAM] at low high
  have location : w 38 = w 6 := by linear_combination low
  have upper : w 39 = 0 := by linear_combination high
  have read (i : Fin 3) (cell : Cell)
      (address : importedConstraintsMemoryPorts[i].address.code w = cell.addressCode) :=
    native_history_read epoch (columns := importedConstraintsTraceColumns)
      (ports := importedConstraintsMemoryPorts) rfl rfl rfl history
      (by simp [importedConstraintsMemoryPorts]) address
  have left := read 0 (.register entry.data.rs1) (by
    simpa [importedConstraintsMemoryPorts, MemoryAddress.code, Cell.addressCode, importedConstraintsDecoderColumns] using
      congrArg (Nat.pair 0) indices.1)
  have right := read 1 (.register entry.data.rs2) (by
    simpa [importedConstraintsMemoryPorts, MemoryAddress.code, Cell.addressCode,
      noRAM, location, upper, pairCode, importedConstraintsDecoderColumns] using congrArg (Nat.pair 0) indices.2.1)
  simpa [importedConstraintsMemoryPorts, MemoryPort.readCode, pairCode, memoryWord, Cell.read] using And.intro left right

end Airbender.UnifiedReduced.Proofs
