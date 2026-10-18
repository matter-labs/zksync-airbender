import Airbender.Proofs.Trace.PortReads
import Airbender.Proofs.Sail.CheckedMemory

namespace Airbender.Trace.Proofs
open Reference.RiscV.Sail Reference.Sail

/-- Actual GPR/RAM writes preserve the public Machine/PMP/PMA configuration. -/
theorem cell_write_configuration {before after : State} {cell : Cell} {value : BitVec 32}
    (configuration : FlatMemoryConfiguration before)
    (written : run (cell.write value) before = .ok () after) :
    FlatMemoryConfiguration after := by
  cases cell with
  | register index => exact configuration_gpr_write configuration index value written
  | ram address =>
    have same := (EStateM.Result.ok.inj ((write_word_state before address value).symm.trans written)).2
    subst after
    exact configuration_word_write configuration address.toNat value

/-- Every realized native prefix retains the original public configuration. -/
theorem sail_history_configuration {cells : List Cell} {events : List MemoryAccess}
    {before after : State} (history : SailHistory cells events before after)
    (configuration : FlatMemoryConfiguration before) : FlatMemoryConfiguration after := by
  induction history with
  | nil => exact configuration
  | cons past cell member address read written ih => exact cell_write_configuration (ih configuration) written

end Airbender.Trace.Proofs
