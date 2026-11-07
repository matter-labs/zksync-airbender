import Airbender.Proofs.SubwordMemory.RowModel
import Airbender.Proofs.Sail.VirtualMemory

namespace Airbender.SubwordMemory.Proofs
open Airbender.Reference.RiscV Airbender.Reference.Sail
open _root_.Sail.ArchSem

/-- Platform transport follows from configuration and the derived address domain;
    no successful Sail virtual access is supplied by the caller. -/
theorem memory_access [MemoryPlatform SailRV32.exception] {input : Input}
    (configuration : Sail.FlatMemoryConfiguration input.before)
    (aligned : (input.source.toBitVec + input.immediate.toBitVec).toNat %
      (if input.byte then 1 else 2) = 0)
    (ordinary : Sail.PlatformWordAddress (input.source.toBitVec + input.immediate.toBitVec)) :
    MemoryAccess input := by
  have width : (if input.byte then 1 else 2) = 1 ∨
      (if input.byte then 1 else 2) = 2 ∨ (if input.byte then 1 else 2) = 4 := by
    cases input.byte <;> simp
  constructor
  · intro _ nextPC value registerRead bytes
    apply Sail.virtual_memory_read_platform width (Sail.configuration_next_pc_write configuration nextPC)
      input.rs1 input.immediate.toBitVec registerRead aligned ordinary
    exact Sail.read_memory_frame width (before := input.before)
      (after := { input.before with regs := input.before.regs.insert .nextPC nextPC }) rfl bytes
  · intro _ nextPC value registerRead
    obtain ⟨after, write, _⟩ := Sail.write_memory_frame
      (by cases input.byte <;> simp : (if input.byte then 1 else 2) ≤ 4)
      (input.source.toBitVec + input.immediate.toBitVec) value
      { input.before with regs := input.before.regs.insert .nextPC nextPC }
    rw [Sail.virtual_memory_write_platform width (Sail.configuration_next_pc_write configuration nextPC)
      input.rs1 input.immediate.toBitVec registerRead aligned ordinary value write]
    rw [run_bind_of_ok _ _ _ _ _ write]
    rfl

end Airbender.SubwordMemory.Proofs
