import Airbender.Review.Circuits.UnifiedReduced.Control
import Airbender.Proofs.UnifiedReduced.Retirement

namespace Airbender.UnifiedReduced.Proofs
open Arithmetic Reference.RiscV.Sail Reference.Sail Trace Trace.Proofs
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000

theorem store_effects {p : Nat} [Fact p.Prime] {w : Nat → ZMod p} {cells : List Cell}
    (store : w 29 = 1) (addressBound : (Word.mk (w 44).val (w 45).val).Bounded) (epoch : Nat) {before after : State}
    (history : SailHistory cells (rowEvents epoch (⟨.machine, w⟩ : Row p UnifiedFamily)).reverse before after) :
    run (projectedStep zeroRegister ⟨⟨0, 0⟩, Control.finalPC w⟩
      (writeMemory (size := 4) (Word.mk (w 44).val (w 45).val).toBitVec (Control.destination w).toBitVec))
      (retiredState before (Control.initialPC w).toBitVec) =
      .ok SailRV32.Functions.RETIRE_SUCCESS (retiredState after (Control.finalPC w).toBitVec) := by
  have normalized := retired_state_history history (Control.initialPC w).toBitVec
  have write := native_history_write epoch rfl rfl rfl normalized
    (ports := importedConstraintsMemoryPorts) (port := importedConstraintsMemoryPorts[2])
    (cell := Cell.ram (Word.mk (w 44).val (w 45).val).toBitVec)
    (by simp [importedConstraintsMemoryPorts]) ?_
  · have projection := projected_step_of_cell_write
      (.ram (Word.mk (w 44).val (w 45).val).toBitVec) (Control.destination w).toBitVec
      (Control.finalPC w) (by simpa [importedConstraintsMemoryPorts, MemoryPort.writeCode,
        pairCode, memoryWord, Control.destination, Word.toBitVec, Word.value] using write)
    simpa only [Cell.write, Word.toBitVec, Word.value, retired_state_overwrite] using projection
  · have canonical : Word.ofBitVec (Word.mk (w 44).val (w 45).val).toBitVec =
        Word.mk (w 44).val (w 45).val := by
      dsimp only [Word.ofBitVec]
      rw [Word.toBitVec_toNat addressBound]
      apply congrArg₂ Word.mk
      all_goals dsimp [Word.value, limbBase, Word.Bounded] at *
      all_goals omega
    simp [importedConstraintsMemoryPorts, MemoryAddress.code, Cell.addressCode, store, pairCode, canonical]
    simpa only [Nat.cast_one] using ZMod.val_natCast_of_lt (Fact.out : Nat.Prime p).one_lt

end Airbender.UnifiedReduced.Proofs
