import Airbender.Proofs.Trace.Families.WordMemory.ZeroRegister
import Airbender.Proofs.Trace.PortReads

namespace Airbender.WordMemory.Proofs
open Trace Reference.RiscV.Sail Reference.Sail

/-- All three native ports read the same instruction pre-state. The first two
    refresh only timestamps, even when their addresses alias. -/
theorem row_history_read {cells : List Cell} {row : Row p WordMemoryFamily} (epoch : Nat)
    {before after : State}
    (history : SailHistory cells (rowEvents epoch row).reverse before after)
    {port : MemoryPort} (present : port ∈ row.ports) {cell : Cell}
    (address : port.address.code row.assignment = cell.addressCode) :
    cell.read before = .ok (memoryWord (port.readCode row.assignment)) before := by
  cases row with
  | mk family w =>
    cases family
    exact Trace.Proofs.native_history_read epoch rfl rfl rfl history present address

/-- The final mixed port performs the actual native register/RAM write. -/
theorem row_history_write {cells : List Cell} {row : Row p WordMemoryFamily} (epoch : Nat)
    {before after : State}
    (history : SailHistory cells (rowEvents epoch row).reverse before after)
    {port : MemoryPort} (last : row.ports.toList.getLast? = some port) {cell : Cell}
    (address : port.address.code row.assignment = cell.addressCode) :
    run (cell.write (memoryWord (port.writeCode row.assignment))) before = .ok () after := by
  cases row with
  | mk family w =>
    cases family
    exact Trace.Proofs.native_history_write epoch rfl rfl rfl history last address

/-- Public decoder indices identify the actual source-register read. -/
theorem history_source_read (hp : Arithmetic.limbBase < p)
    {cells : List Cell} {w : Nat → ZMod p} (epoch : Nat) {before after : State}
    (history : SailHistory cells
      (rowEvents epoch (⟨.wordMemory, w⟩ : Row p WordMemoryFamily)).reverse before after)
    {entry : ProgramEntry WordMemoryFamily}
    (query : (⟨.wordMemory, w⟩ : Row p WordMemoryFamily).decoderQuery = entry.query) :
    run (SailRV32.Functions.rX_bits (.Regidx entry.data.rs1)) before =
      .ok (sourceWord w).toBitVec before := by
  have source := (Trace.Proofs.native_query_indices hp query).1
  change (w 5).val = entry.data.rs1.toNat at source
  have read := row_history_read epoch history
    (port := importedConstraintsMemoryPorts[0])
    (by change _ ∈ importedConstraintsMemoryPorts; simp [importedConstraintsMemoryPorts])
    (cell := Cell.register entry.data.rs1)
    (by change Nat.pair 0 (Nat.pair (w 5).val 0) = Nat.pair 0 (Nat.pair entry.data.rs1.toNat 0)
        rw [source])
  simpa [Cell.read, MemoryPort.readCode, WordColumns.code, WordColumns.evaluate,
    importedConstraintsMemoryPorts, memoryWord, Nat.unpair_pair, sourceWord] using read

end Airbender.WordMemory.Proofs
