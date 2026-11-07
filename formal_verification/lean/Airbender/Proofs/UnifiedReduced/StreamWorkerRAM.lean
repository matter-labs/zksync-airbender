import Airbender.Proofs.UnifiedReduced.StreamWorkerABI
import Airbender.Review.Helpers.Context.ExternalBoundary.WorkerRAM

namespace Airbender.UnifiedReduced.Caller.Stream.Proofs
open Arithmetic Trace Reference.RiscV.Sail
set_option warningAsError true

/-- The exact native worker-port domain supplies each indirect RAM lower bound. -/
theorem worker_indirect_ram_of_binding [Fact p.Prime]
    {workers : List (Delegation.Row p)}
    (ram : ExternalBoundary.WorkerRAM.Binding workers)
    {worker : Delegation.Row p} (member : worker ∈ workers)
    {port : MemoryPort} (present : port ∈ worker.ports)
    {indirect : Verification.IndirectPort} (shape : port.address = .indirect indirect) :
    ROM.limit ≤ (indirect.address worker.assignment).toNat := by
  obtain ⟨location, code⟩ := ram worker member port present
  have actual : location.cell.addressCode = (.indirect indirect : MemoryAddress).code worker.assignment := by
    rw [← code, shape]
  have same := Delegation.Proofs.indirect_cell actual
  cases location with
  | register index => cases same
  | ram address outside =>
    change Cell.ram address = Cell.ram (indirect.address worker.assignment) at same
    have equal := Cell.ram.inj same
    exact equal ▸ outside

/-- Exact worker-domain binding bounds a RAM cell identified by its native code. -/
theorem worker_cell_ram_of_binding [Fact p.Prime]
    {workers : List (Delegation.Row p)}
    (ram : ExternalBoundary.WorkerRAM.Binding workers)
    {worker : Delegation.Row p} (member : worker ∈ workers)
    {port : MemoryPort} (present : port ∈ worker.ports)
    {address : BitVec 32}
    (code : (Cell.ram address).addressCode = port.address.code worker.assignment) :
    ROM.limit ≤ address.toNat := by
  obtain ⟨location, actual⟩ := ram worker member port present
  have same : location.cell = Cell.ram address :=
    Trace.Proofs.cell_address_injective (actual.symm.trans code.symm)
  cases location with
  | register index => cases same
  | ram target outside =>
    change Cell.ram target = Cell.ram address at same
    exact Cell.ram.inj same ▸ outside

end Airbender.UnifiedReduced.Caller.Stream.Proofs
