import Airbender.Proofs.Trace.Families.JumpBranchSlt.ZeroRegister
import Airbender.Proofs.Trace.PortReads

namespace Airbender.JumpBranchSlt.Proofs
open Trace Reference.RiscV.Sail Reference.Sail

/-- All three native ports read the same instruction pre-state. The first two
    refresh only timestamps, even when their addresses alias. -/
theorem row_history_read {cells : List Cell} {row : Row p JumpBranchSltFamily} (epoch : Nat)
    {before after : State}
    (history : SailHistory cells (rowEvents epoch row).reverse before after)
    {port : MemoryPort} (present : port ∈ row.ports) {cell : Cell}
    (address : port.address.code row.assignment = cell.addressCode) :
    cell.read before = .ok (memoryWord (port.readCode row.assignment)) before := by
  cases row with
  | mk family w =>
    cases family
    exact Trace.Proofs.native_history_read epoch rfl rfl rfl history present address

/-- The final port performs the actual masked native register write. -/
theorem row_history_write {cells : List Cell} {row : Row p JumpBranchSltFamily} (epoch : Nat)
    {before after : State}
    (history : SailHistory cells (rowEvents epoch row).reverse before after)
    {port : MemoryPort} (last : row.ports.toList.getLast? = some port) {cell : Cell}
    (address : port.address.code row.assignment = cell.addressCode) :
    run (cell.write (memoryWord (port.writeCode row.assignment))) before = .ok () after := by
  cases row with
  | mk family w =>
    cases family
    exact Trace.Proofs.native_history_write epoch rfl rfl rfl history last address

/-- The ten-column decoder identifies both actual Sail source registers.
    Their values come from the grouped native history, including aliases. -/
theorem history_register_reads (hp : Arithmetic.limbBase < p)
    {cells : List Cell} {w : Nat → ZMod p} (epoch : Nat) {before after : State}
    (history : SailHistory cells (rowEvents epoch (⟨.jumpBranchSlt, w⟩ : Row p JumpBranchSltFamily)).reverse before after)
    {entry : ProgramEntry} (query : (⟨.jumpBranchSlt, w⟩ : Row p JumpBranchSltFamily).decoderQuery = entry.query) :
    run (SailRV32.Functions.rX_bits (.Regidx entry.data.rs1)) before =
      .ok (memoryWord (importedConstraintsMemoryPorts[0].readCode w)) before ∧
    run (SailRV32.Functions.rX_bits (.Regidx entry.data.rs2)) before =
      .ok (memoryWord (importedConstraintsMemoryPorts[1].readCode w)) before := by
  obtain ⟨left, right, _⟩ := Trace.Proofs.native_query_indices hp query
  change (w 5).val = entry.data.rs1.toNat at left
  change (w 6).val = entry.data.rs2.toNat at right
  constructor
  · exact row_history_read epoch history
      (port := importedConstraintsMemoryPorts[0])
      (by change importedConstraintsMemoryPorts[0] ∈ importedConstraintsMemoryPorts
          simp [importedConstraintsMemoryPorts])
      (cell := Cell.register entry.data.rs1)
      (by change Nat.pair 0 (Nat.pair (w 5).val 0) = Nat.pair 0 (Nat.pair entry.data.rs1.toNat 0)
          rw [left])
  · exact row_history_read epoch history
      (port := importedConstraintsMemoryPorts[1])
      (by change importedConstraintsMemoryPorts[1] ∈ importedConstraintsMemoryPorts
          simp [importedConstraintsMemoryPorts])
      (cell := Cell.register entry.data.rs2)
      (by change Nat.pair 0 (Nat.pair (w 6).val 0) = Nat.pair 0 (Nat.pair entry.data.rs2.toNat 0)
          rw [right])

/-- The decoded destination register receives the actual masked native write. -/
theorem history_register_write (hp : Arithmetic.limbBase < p)
    {cells : List Cell} {w : Nat → ZMod p} (epoch : Nat) {before after : State}
    (history : SailHistory cells (rowEvents epoch (⟨.jumpBranchSlt, w⟩ : Row p JumpBranchSltFamily)).reverse before after)
    {entry : ProgramEntry} (query : (⟨.jumpBranchSlt, w⟩ : Row p JumpBranchSltFamily).decoderQuery = entry.query) :
    run (SailRV32.Functions.wX_bits (.Regidx entry.data.rd)
      (memoryWord (importedConstraintsMemoryPorts[2].writeCode w))) before = .ok () after := by
  have destination := (Trace.Proofs.native_query_indices hp query).2.2
  change (w 7).val = entry.data.rd.toNat at destination
  exact row_history_write epoch history
    (port := importedConstraintsMemoryPorts[2]) (by rfl)
    (cell := Cell.register entry.data.rd)
    (by change Nat.pair 0 (Nat.pair (w 7).val 0) = Nat.pair 0 (Nat.pair entry.data.rd.toNat 0)
        rw [destination])

/-- The native old destination read also uses the instruction pre-state. -/
theorem history_destination_read (hp : Arithmetic.limbBase < p)
    {cells : List Cell} {w : Nat → ZMod p} (epoch : Nat) {before after : State}
    (history : SailHistory cells
      (rowEvents epoch (⟨.jumpBranchSlt, w⟩ : Row p JumpBranchSltFamily)).reverse before after)
    {entry : ProgramEntry} (query : (⟨.jumpBranchSlt, w⟩ : Row p JumpBranchSltFamily).decoderQuery = entry.query) :
    run (SailRV32.Functions.rX_bits (.Regidx entry.data.rd)) before =
      .ok (memoryWord (importedConstraintsMemoryPorts[2].readCode w)) before := by
  have destination := (Trace.Proofs.native_query_indices hp query).2.2
  change (w 7).val = entry.data.rd.toNat at destination
  exact row_history_read epoch history
    (port := importedConstraintsMemoryPorts[2])
    (by change _ ∈ importedConstraintsMemoryPorts; simp [importedConstraintsMemoryPorts])
    (cell := Cell.register entry.data.rd)
    (by change Nat.pair 0 (Nat.pair (w 7).val 0) = Nat.pair 0 (Nat.pair entry.data.rd.toNat 0)
        rw [destination])

end Airbender.JumpBranchSlt.Proofs
