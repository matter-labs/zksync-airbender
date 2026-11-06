import Slop.WordMemory.RowModel
import Slop.Sail.VirtualMemory

namespace Airbender.WordMemory.Proofs
open Airbender.Reference.RiscV Airbender.Reference.Sail
open _root_.Sail.ArchSem

/-- The existing family transport interface follows from public configuration
    and the effective address domain, without assuming a virtual access result. -/
theorem memory_access  {input : Input}
    (configuration : Sail.Configured input.before)
    (aligned : (input.source.toBitVec + input.immediate.toBitVec).toNat % 4 = 0)
    (ordinary : Sail.OrdinaryWordAddress (input.source.toBitVec + input.immediate.toBitVec))
    (ram : input.store = true →
      Sail.Configuration.ROM_END ≤ (input.source.toBitVec + input.immediate.toBitVec).toNat) :
    MemoryAccess input := by
  constructor
  · intro _ nextPC value registerRead bytes
    apply Sail.virtual_word_read (Sail.configuration_next_pc_write configuration nextPC)
      input.rs1 input.immediate.toBitVec registerRead aligned ordinary
    exact Sail.read_word_frame (before := input.before)
      (after := { input.before with regs := input.before.regs.insert .nextPC nextPC }) rfl bytes
  · intro store nextPC value registerRead
    rw [Sail.virtual_word_write (Sail.configuration_next_pc_write configuration nextPC)
      input.rs1 input.immediate.toBitVec registerRead aligned ordinary (ram store) value]
    rw [run_bind_of_ok _ _ _ _ _ (Sail.write_word_state _ _ value)]
    rfl

end Airbender.WordMemory.Proofs
